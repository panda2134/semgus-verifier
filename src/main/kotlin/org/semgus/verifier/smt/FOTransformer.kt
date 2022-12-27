package org.semgus.verifier.smt

import com.maxadamski.illogical.*
import org.semgus.java.`object`.SmtTerm
import scala.jdk.javaapi.CollectionConverters
import java.lang.RuntimeException

/**
 * Currently, we do not support = for boolean values.
 * That's because parsing this requires type deduction, which is the next goal
 *
 */
class FOTransformer(term: SmtTerm) {
    private var reverseMapping = mutableMapOf<String, String>()
    val illogicalForm: Form

    init {
        illogicalForm = toIllogicalTerm(term) as Form
        println(`TextFormatter$`.`MODULE$`.fmt(illogicalForm))
        val skolem = `Skolemizer$`.`MODULE$`.skolemized(illogicalForm)
        fun f(x: Form): Form =
            when (x) {
                is Qu -> f(x.form())
                else -> x
            }
        val core = Not(f(skolem)).simplifying()
        println(`TextFormatter$`.`MODULE$`.fmt(core))
    }

    private fun toIllogicalTerm(term: SmtTerm, useFunc: Boolean = false): Node =
        when (term) {
            is SmtTerm.Quantifier -> term.bindings.map { v ->
                val newName = "var${reverseMapping.size}"
                reverseMapping[newName] = v.name
                newName
            }.foldRight(toIllogicalTerm(term.child) as Form) { s, form ->
                Qu(
                    if (term.type == SmtTerm.Quantifier.Type.EXISTS) {
                        `EXISTS$`.`MODULE$`
                    } else {
                        `FORALL$`.`MODULE$`
                    },
                    Var(s),
                    form
                )
            }
            is SmtTerm.Application -> {
                val logicalTokens = listOf("and", "or", "not", "=>")

                if (term.name.name in logicalTokens) {
                    val args = term.arguments.map { v ->
                        toIllogicalTerm(v.term, false) as Form
                    }

                    when(term.name.name) {
                        "and" -> args.reduce {s, t -> Op(s, `AND$`.`MODULE$`, t) }
                        "or" -> args.reduce {s, t -> Op(s, `OR$`.`MODULE$`, t) }
                        "=>" -> args.reduce {s, t -> Op(s, `IMP$`.`MODULE$`, t) }
                        "not" -> {
                            assert(args.size == 1)
                            Not(args.first())
                        }
                        else -> throw RuntimeException("impossible!")
                    }
                } else {
                    val args = term.arguments.map { v ->
                        toIllogicalTerm(v.term, true) as Term
                    }
                    if (term.arguments.isNotEmpty()) {
                        val newName = "${if (useFunc) "func" else "pred"}${reverseMapping.size}"
                        reverseMapping[newName] = term.name.name
                        if (useFunc) Func(newName,  CollectionConverters.asScala(args).toList())
                        else Pred(newName, CollectionConverters.asScala(args).toList())
                    } else {
                        val newName = "var${reverseMapping.size}"
                        reverseMapping[newName] = term.name.name
                        Var(newName)
                    }
                }
            }
            is SmtTerm.Variable -> {
                val newName = "var${reverseMapping.size}"
                reverseMapping[newName] = term.name
                Var(newName)
            }
            is SmtTerm.CString -> {
                val newName = "@s${reverseMapping.size}"
                reverseMapping[newName] = term.value
                Con(newName)
            }
            is SmtTerm.CNumber -> {
                val newName = "@n${reverseMapping.size}"
                reverseMapping[newName] = term.value.toString()
                Con(newName)
            }
            is SmtTerm.CBitVector -> {
                val lit =
                    "#x" + term.value.toByteArray().reversed().joinToString { v -> "%02x".format(v) }
                val newName = "@n${reverseMapping.size}"
                reverseMapping[newName] = lit
                Con(newName)
            }

            else -> throw IllegalArgumentException("cannot convert this into s-expr")
        }

}