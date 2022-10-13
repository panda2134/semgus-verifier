package org.semgus.verifier.smt

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import de.tudresden.inf.lat.jsexp.SexpList
import de.tudresden.inf.lat.jsexp.SexpString
import org.semgus.verifier.frontend.VerificationTarget
import org.semgus.verifier.walk.ProgramWalker
import org.semgus.java.`object`.SmtTerm
import org.semgus.java.`object`.TypedVar
import java.nio.file.Path
import java.lang.ProcessBuilder
import java.lang.ProcessBuilder.Redirect
import java.lang.RuntimeException
import java.util.concurrent.TimeUnit
import kotlin.io.path.createTempFile

class SmtAdapter(
    val target: VerificationTarget,
    val rootRuleName: String,
    val instantiatedRules: List<ProgramWalker.InstantiatedSemanticRule>
    ) {
    private val prelude = """
        (set-logic HORN)
        (set-option :fp.engine spacer)
        (set-option :fp.xform.slice false)
        (set-option :fp.xform.inline_linear false)
        (set-option :fp.xform.inline_eager false)
        (set-option :parallel.enable true)
    """.trimIndent()

    private var cexArgSignature: List<TypedVar>? = null

    /**
     * @return (program verified?, counterexamples)
     */
    fun runZ3AndParseModel(path: Path): Pair<Boolean, List<Pair<TypedVar, String>>> {
        val proc = ProcessBuilder(listOf("z3", path.toAbsolutePath().toString()))
            .redirectOutput(Redirect.PIPE)
            .redirectError(Redirect.PIPE)
            .start()
        proc.waitFor(24, TimeUnit.HOURS)
        val stderr = proc.errorStream.bufferedReader().readLines()
        val stdout = proc.inputStream.bufferedReader().readLines()
        if (stderr.isNotEmpty()) {
            throw RuntimeException("Z3 error: \n ${stderr.joinToString("\n")}")
        }
        when (stdout.first()) {
            "unsat" -> { return Pair(true, listOf()) }
            "unknown" -> { throw RuntimeException("Z3 gives unknown model") }
            "sat" -> {
                val sExpression = SexpFactory.parse(stdout.drop(1).joinToString("\n"))
                val mp = extractModusPonens(sExpression)!!
                var argsAsStrings: List<String>? = null
                for (child in mp.iterator()) {
                    if (child !is SexpList) continue
                    val subChildren = child.iterator().asSequence().toList()
                    val tactic = subChildren.first()
                    if (tactic !is SexpString || tactic.toString() != "asserted") {
                        continue
                    }
                    val impliesRule = (subChildren[1] as? SexpList) ?: continue
                    val application = impliesRule.iterator().asSequence().toList()[1]
                    val applicationList = (application as? SexpList) ?: continue
                    val args = applicationList.iterator().asSequence().toList().drop(1)
                    argsAsStrings = args.map { v -> (v as SexpString).toString() }
                }
                return Pair(false, cexArgSignature!!.zip(argsAsStrings!!).toList())
            }
            else -> { throw IllegalArgumentException("malformed z3 result!") }
        }
    }

    private fun extractModusPonens (input: Sexp): Sexp? {
        if (input !is SexpList) return null
        val children = input.iterator().asSequence().toList()
        val f = children.first()
        if (f !is SexpString) {
            return null
        }
        return when (f.toString()) {
            "let" -> extractModusPonens(children[2])
            "mp" -> input
            else -> null
        }
    }

    fun generateSmtFile(): Path {
        val (fullConstraint, quantifiedChild, semOccurrence) = verifyAndExtract()

        val path = createTempFile("semgus-verification", ".smt2")
        val w = path.toFile().printWriter()

        val constraint = quantifiedChild.arguments.drop(1).first()
        w.println("; prelude")
        w.println(prelude)
        w.println()

        w.println("; relation declarations")
        cexArgSignature = fullConstraint.bindings
        w.println("(declare-rel Counterex (${fullConstraint.bindings.joinToString(" ") { v -> v.type.name }}))")
        val printedRules = mutableSetOf<String>()
        for (rule in instantiatedRules) {
            if (rule.head.name in printedRules) continue
            printedRules.add(rule.head.name)
            w.println("(declare-rel ${rule.head.name} (${rule.head.arguments.joinToString(" ") { v -> v.type.name }}))")
        }
        w.println()
        w.println("; semantic rules, instantiated with the given AST")
        for ((index, rule) in instantiatedRules.withIndex()) {
            val printed = mutableSetOf<String>()
            val printArgs = { xs: List<TypedVar> ->
                for (arg in xs) {
                    val name = "$${index}$${arg.name}"
                    if (name in printed) continue
                    printed.add(name)
                    w.println("(declare-var $name ${arg.type})")
                }
            }
            for (premise in rule.bodyRelations) {
                printArgs(premise.arguments)
            }
            printArgs(rule.head.arguments)
            w.println(rule.toSExpression("$${index}$"))
            w.println()
        }
        w.println()
        w.println("; verification condition")
        val rootRuleSExpr = "($rootRuleName ${
            semOccurrence.arguments
                .filter { v -> v.type.name != target.problem.targetNonTerminal.name }
                .joinToString(" ") { v -> v.term.toSExpression() }
        })"
        for (binding in fullConstraint.bindings) {
            w.println("(declare-var ${binding.name} ${binding.type})")
        }
        w.println("(rule (=> (and $rootRuleSExpr (not ${constraint.term.toSExpression()}))\n" +
                "          (Counterex ${fullConstraint.bindings.joinToString(" ") { v -> v.name }}) ))"
        )
        w.println()
        w.println("; query for counterexamples")
        w.println("(query Counterex :print-certificate true)")
        w.close()

        return path
    }

    private fun verifyAndExtract(): Triple<SmtTerm.Quantifier, SmtTerm.Application, SmtTerm.Application> {
        // only allow 1 constraint
        assert(target.problem.constraints.size == 1)
        val fullConstraint = target.problem.constraints.first() as SmtTerm.Quantifier
        // only allow forall now
        assert(fullConstraint.type == SmtTerm.Quantifier.Type.FOR_ALL)

        // inner parts of the quantified expression
        val quantifiedChild = fullConstraint.child as SmtTerm.Application
        assert(quantifiedChild.name.name == "=>" && quantifiedChild.arguments.size == 2)
        val semOccurrence = quantifiedChild.arguments.first()!!.term as SmtTerm.Application

        // extract the premise, which should be a semantic relation application
        val semRelationHead = target.problem.targetNonTerminal.productions.entries.first()
            .value.semanticRules.first()!!.head
        assert(semOccurrence.name.name == semRelationHead.name)
        val programArgPos =
            semRelationHead.arguments.indexOfFirst { v -> v.type.name == target.problem.targetNonTerminal.name }
        // ensure that the semantic relation is applied on the synthesis target
        assert((semOccurrence.arguments[programArgPos].term as SmtTerm.Application).name.name == target.problem.targetName)

        return Triple(fullConstraint, quantifiedChild, semOccurrence)
    }
}