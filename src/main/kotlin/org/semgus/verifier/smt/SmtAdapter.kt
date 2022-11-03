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
        (set-option :fp.spacer.arith.solver 6)
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
            throw RuntimeException("Z3 error: \n${stderr.joinToString("\n")}")
        }
        if (stdout.any { x -> x.startsWith("(error ") }) {
            throw RuntimeException("Z3 error: \n${stdout.joinToString("\n")}")
        }
        when (val out = stdout.first()) {
            "unsat" -> {
                return Pair(true, listOf())
            }

            "unknown" -> {
                throw RuntimeException("Z3 gives unknown model")
            }

            "sat" -> {
                val sExpression = SexpFactory.parse(stdout.drop(1).joinToString("\n"))
                val letExpr = extractLet(sExpression)
                val cex = letExpr.flatMap { v -> extractCounterExample(v.second) }
                println(cex)
                val argsAsStrings = cex.last().drop(1).map { v ->
                    when (v) {
                        is SexpString -> v.toString()
                        is SexpList -> {
                            if (v.length != 2 || v.first() !is SexpString || v.drop(1).first() !is SexpString)
                                return@map v.toString()
                            val p = v.first() as SexpString
                            val n = v.drop(1).first() as SexpString
                            if (p.toString() != "-") {
                                return@map v.toString()
                            }
                            "-$n"
                        }

                        else -> throw IllegalStateException("unrecognized argument: $v")
                    }
                }
                return Pair(false, cexArgSignature!!.zip(argsAsStrings).toList())
            }

            else -> {
                println(out)
                throw IllegalArgumentException("malformed z3 result!")
            }
        }
    }

    private fun extractCounterExample(input: Sexp): List<SexpList> {
        if (input !is SexpList) return listOf()
        val children = input.toList()
        val f = children.first()
        if (f is SexpString && f.toString() == "Counterex") {
            return listOf(input)
        }
        return children.flatMap { v -> extractCounterExample(v) }
    }

    private fun extractLet(input: Sexp): List<Pair<String, Sexp>> {
        if (input !is SexpList) return listOf()
        val children = input.toList()
        val f = children.first()
        if (f !is SexpString) {
            return listOf()
        }
        return when (f.toString()) {
            "let" -> {
                val declList = children[1] as SexpList
                (declList.map { v ->
                    val x = v as SexpList
                    assert(x.length == 2)
                    Pair((x[0] as SexpString).toString(), x[1] as Sexp)
                }) + extractLet(children[2])
            }

            else -> listOf()
        }
    }

    fun generateSmtFile(): Path {
        val (fullConstraint, quantifiedChild, semOccurrence) = verifyAndExtract()

        val path = createTempFile("semgus-verification-", ".smt2")
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
        w.println(
            "(rule (=> (and $rootRuleSExpr (not ${constraint.term.toSExpression()}))\n" +
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