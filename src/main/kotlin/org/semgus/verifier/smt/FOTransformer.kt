package org.semgus.verifier.smt

import com.maxadamski.illogical.*
import org.semgus.java.`object`.SmtTerm
import scala.collection.immutable.Map
import scala.jdk.javaapi.CollectionConverters
import java.lang.RuntimeException
import java.util.*

class FOTransformer() {
    private var illogicalForm: Form? = null
    var declaredRelation = mapOf<String, Optional<List<String>>>()
    var declaredVars = mapOf<String, String>()

    private fun skolemize(form: Form): Pair<Form, Set<Term>> {
        val partialPNF = form.simplifying().partialPNF()
        val skolemSubMethod = `Skolemizer$`.`MODULE$`::class.java.getDeclaredMethod("skolemSub", scala.collection.immutable.List::class.java)
        skolemSubMethod.isAccessible = true
        val subs = skolemSubMethod.invoke(`Skolemizer$`.`MODULE$`, partialPNF._2) as scala.collection.immutable.Set<Sub>?
        val result = partialPNF._1.cnf().substituting(subs)
        // TODO: add all vars in partialPnf prefix into the term set returned
        val newTerms = CollectionConverters.asJava(subs!!.map { x -> x.t() }.toSet<Term>())
        return Pair(result, newTerms as Set<Term>)
    }

    private fun findDNFClauses(x: Form): List<Form> =
        when (x) {
            is Op -> {
                if (x.token() != `OR$`.`MODULE$`) {
                    listOf(x)
                } else {
                    findDNFClauses(x.leftForm()) + findDNFClauses(x.rightForm())
                }
            }
            else -> listOf(x)
        }

    fun toDNFClauseList(term: SmtTerm): Pair<List<Form>, Set<Term>> {
        illogicalForm = toIllogicalTerm(term) as Form
        val mapWrapper = CollectionConverters.asScala(declaredVars.map { (k, v) -> Pair(k, ConcreteType(v) as NodeType) }.toMap())
        val ctx = Map.from(mapWrapper)

        illogicalForm!!.typeCheck(ctx)
        println("[original] ${`SexprFormatter$`.`MODULE$`.formatted(illogicalForm)}")
        val (skolem, subs) = this.skolemize(illogicalForm!!)
        skolem.typeCheck(ctx)
        println("[skolem] ${`SexprFormatter$`.`MODULE$`.formatted(skolem)}")
        val partialPNF = skolem.partialPNF()
        println("[partialPNF] ${`SexprFormatter$`.`MODULE$`.formatted(partialPNF._1)}")
        val core = Not(partialPNF._1).simplifying()
        val dnf = core.dnf()
        println("[core] ${`SexprFormatter$`.`MODULE$`.formatted(core)}")
        println("[dnf] ${`SexprFormatter$`.`MODULE$`.formatted(dnf)}")

        return Pair(findDNFClauses(dnf), subs)
    }

    private fun toIllogicalTerm(term: SmtTerm, useFunc: Boolean = false): Node =
        when (term) {
            is SmtTerm.Quantifier -> term.bindings.map { v ->
                Pair(v.name, v.type.toSExpressionType())
            }.foldRight(toIllogicalTerm(term.child) as Form) { (s, ty), form ->
                Qu(
                    if (term.type == SmtTerm.Quantifier.Type.EXISTS) {
                        `EXISTS$`.`MODULE$`
                    } else {
                        `FORALL$`.`MODULE$`
                    },
                    Var(s, ConcreteType(ty)),
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
                        "=>" -> args.reduceRight {s, t -> Op(s, `IMP$`.`MODULE$`, t) }
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
                    // working around a bug in semgus-parser that treats (mul-by-while) as a predicate
                    if (term.arguments.isNotEmpty()) {
                        val typing = declaredRelation[term.name.name]
                        if (!useFunc && typing == null) {
                            throw IllegalArgumentException("unknown predicate ${term.name.name}")
                        }

                        // TODO: consider typing here
                        if (useFunc) Func(
                            term.name.name,
                            CollectionConverters.asScala(args).toList(),
                            scala.Option.apply(null)
                        )
                        else Pred(term.name.name, CollectionConverters.asScala(args).toList(), scala.Option.apply(null))
                    }  else {
                        Var(term.name.name, `AnyType$`.`MODULE$`)
                    }
                }
            }
            is SmtTerm.Variable -> {
                Var(term.name, ConcreteType(term.type.toSExpressionType()))
            }
            is SmtTerm.CString -> {
                Con("\"${term.value}\"", ConcreteType("String"))
            }
            is SmtTerm.CNumber -> {
                Con(term.value.toString(), ConcreteType("Int"))
            }
            is SmtTerm.CBitVector -> {
                val lit =
                    "#x" + term.value.toByteArray().reversed().joinToString { v -> "%02x".format(v) }
                Con(lit, ConcreteType("(_ BitVec ${term.size})"))
            }

            else -> throw IllegalArgumentException("cannot convert this into s-expr")
        }

}