package org.semgus.verifier.smt

import com.maxadamski.illogical.*
import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import de.tudresden.inf.lat.jsexp.SexpList
import de.tudresden.inf.lat.jsexp.SexpString
import org.semgus.verifier.frontend.VerificationTarget
import org.semgus.verifier.walk.ProgramWalker
import org.semgus.java.`object`.SmtTerm
import org.semgus.java.`object`.TypedVar
import scala.jdk.javaapi.CollectionConverters
import java.nio.file.Path
import java.lang.ProcessBuilder
import java.lang.ProcessBuilder.Redirect
import java.lang.RuntimeException
import java.util.*
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
    fun runZ3AndParseModel(path: Path): Pair<Boolean, List<Pair<TypedVar, String>>?> {
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
                return Pair(true, null)
            }

            "unknown" -> {
                throw RuntimeException("Z3 gives unknown model")
            }

            "sat" -> {
                val sExpression = SexpFactory.parse(stdout.drop(1).joinToString("\n"))
                val cex = extractCounterExample(sExpression)
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

    fun generateSmtFile(): List<Path> {
        assert(target.problem.constraints.size == 1)

        val fullConstraint = target.problem.constraints.first() as SmtTerm.Quantifier

        val declaredRelation = mutableMapOf(
            Pair(
                "=",
                Optional.empty<List<String>>()
            ), // temporarily treat = for booleans as predicate, not logical equivalent
            Pair("distinct", Optional.empty<List<String>>()),
            Pair(">", Optional.empty<List<String>>()), // builtins
            Pair("<", Optional.empty<List<String>>()),
            Pair(">=", Optional.empty<List<String>>()),
            Pair("<=", Optional.empty<List<String>>()),
        )
        val declaredVars = mutableMapOf<String, String>()

        val smtFileParts = mutableListOf<String>()

        fun addLine(line: String = "") {
            smtFileParts.add(line)
        }

        addLine("; prelude")
        addLine(prelude)
        addLine()

        addLine("; relation declarations")
        cexArgSignature = fullConstraint.bindings
        addLine("(declare-rel Counterex (${fullConstraint.bindings.joinToString(" ") { v -> v.type.toSExpressionType() }}))")
        declaredRelation["Counterex"] = Optional.of(fullConstraint.bindings.map { v -> v.type.toSExpressionType() })
        val printedRules = mutableSetOf<String>()
        for (rule in instantiatedRules) {
            if (rule.head.name in printedRules) continue
            printedRules.add(rule.head.name)
            addLine("(declare-rel ${rule.head.name} (${rule.head.arguments.joinToString(" ") { v -> v.type.toSExpressionType() }}))")
            declaredRelation[rule.head.name] = Optional.of(rule.head.arguments.map { v -> v.type.toSExpressionType() })
        }
        addLine()
        addLine("; semantic rules, instantiated with the given AST")
        for ((index, rule) in instantiatedRules.withIndex()) {
            val printed = mutableSetOf<String>()
            val printArgs = { xs: List<TypedVar> ->
                for (arg in xs) {
                    val name = "$${index}$${arg.name}"
                    if (name in printed) continue
                    printed.add(name)
                    addLine("(declare-var $name ${arg.type.toSExpressionType()})")
                    declaredVars[name] = arg.type.toSExpressionType()
                }
            }
//            for (premise in rule.bodyRelations) {
//                printArgs(premise.arguments)
//            }
            val typedVars = rule.extractTypedVars()
            printArgs(rule.variables.keys.map { v -> typedVars[v]!! })
            addLine(rule.toSExpression("$${index}$"))
            addLine()
        }
        addLine()
        addLine("; verification condition")

        val semRelationHead = target.problem.targetNonTerminal.productions.entries.first()
            .value.semanticRules.first()!!.head
        val foTransformer = FOTransformer().apply {
            this.declaredRelation = declaredRelation + Pair(
                semRelationHead.name,
                Optional.empty()
            ) // define S.Sem although it will then be substituted
        }
        val (form, subs) = foTransformer.toDNFClauseList(fullConstraint)
//        form.forEach { x -> println(`SexprFormatter$`.`MODULE$`.formatted(x)) }

        return form.withIndex().map { (index, formClause) ->
            val path = createTempFile("semgus-verification-${target.problem.targetName}-${index}", ".smt2")
            val w = path.toFile().printWriter()
            w.println(smtFileParts.joinToString("\n"))
            w.println("; clause $index")

            val formInstantiated = SexprFormatter.formatted(formClause).replace(target.problem.targetName, "")
                .replace(semRelationHead.name, rootRuleName)
            for (binding in fullConstraint.bindings) {
                w.println("(declare-var ${binding.name} ${binding.type.toSExpressionType()})")
            }
            for (n in subs) {
                when (n) {
                    is Var -> {
                        w.println("(declare-var ${n.name()} ${n.typing()})")
                    }

                    is Con -> {
                        w.println("(declare-var ${n.name()} ${n.typing()})")
                    }

                    is Func -> {
                        assert(n.signature().isDefined)
                        val argTypes = CollectionConverters.asJava(n.signature().get()._1)
                        val rtnType = n.signature().get()._2
                        w.println("(declare-fun ${n.name()} (${argTypes.joinToString(" ") { v -> v.toString() }}) ${rtnType.toString()})")
                    }

                    else -> throw IllegalStateException("not possible with pnf & skolemization!")
                }
            }
            val verificationCond =
                "(rule (=> $formInstantiated\n" +
                        "          (Counterex ${fullConstraint.bindings.joinToString(" ") { v -> v.name }}) ))"
            w.println(verificationCond)
            w.println()
            w.println("; query for counterexamples")
            w.println("(query Counterex :print-certificate true)")
            w.close()
            path
        }
    }
}
