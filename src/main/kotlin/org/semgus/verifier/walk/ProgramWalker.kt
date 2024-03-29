package org.semgus.verifier.walk

import org.semgus.java.`object`.AnnotatedVar
import org.semgus.java.`object`.AttributeValue
import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString
import org.semgus.java.`object`.RelationApp
import org.semgus.java.`object`.SmtTerm
import org.semgus.java.`object`.TypedVar
import org.semgus.java.problem.SemgusProblem
import org.semgus.verifier.smt.toSExpression
import org.semgus.verifier.smt.toSExpressionType
import org.semgus.verifier.smt.toSmtName
import org.semgus.verifier.smt.withVariablePrefix
import java.lang.IllegalArgumentException

class ProgramWalker(val program: AList, problem: SemgusProblem) {
    data class InstantiatedSemanticRule (val head: RelationApp, val bodyRelations: List<RelationApp>,
                    val constraint: SmtTerm, val variables: Map<String, AnnotatedVar>,
                    val childTermVars: List<TypedVar>) {
        private fun SmtTerm.extractTypedVars(): Map<String, TypedVar> = when (this) {
            is SmtTerm.Quantifier -> bindings.associateBy { v -> v.name } + child.extractTypedVars()
            is SmtTerm.Variable -> mapOf(Pair(this.name, TypedVar(this.name, this.type)))
            is SmtTerm.Application -> arguments.flatMap { v -> v.term.extractTypedVars().toList() }.toMap()
            is SmtTerm.CString -> mapOf()
            is SmtTerm.CNumber -> mapOf()
            is SmtTerm.CBitVector -> mapOf()
            else -> throw IllegalArgumentException("cannot convert this into s-expr")
        }
        fun toSExpression(variablePrefix: String = ""): String {
            return "(rule (=> (and ${bodyRelations.joinToString(" ") { v->v.toSExpression(variablePrefix) }} ${constraint.withVariablePrefix(variablePrefix).toSExpression()})\n" +
                    "     ${head.toSExpression(variablePrefix)}))"
        }
        fun extractTypedVars(): Map<String, TypedVar> =
            (head.arguments.map { v -> Pair(v.name, v) } +
                    bodyRelations.flatMap { r -> r.arguments.map { v -> Pair(v.name, v) } }).toMap() +
                    constraint.extractTypedVars()
    }
    private val rtgHelper = RegularTreeGrammarHelper(problem.nonTerminals)
    private var semanticCounter = 0
    private val instantiatedSemantics = mutableListOf<InstantiatedSemanticRule>()

    /**
     * @return a pair consisting all new rules and the root semantics rule
     */
    fun traverseProgram(): Pair<List<InstantiatedSemanticRule>, String> {
        instantiatedSemantics.clear()
        semanticCounter = 0
        val root = traverse(program)
        return Pair(instantiatedSemantics.toList(), root)
    }

    /**
     * extracts the semantics name used at the root of the program, without our renaming.
     */
    @Suppress("unused")
    fun extractOriginalRootSemantics(): String {
        val token = program.entries.first()!! as AString
        val rule = rtgHelper.operatorMapping[token.value]!!
        return rule.production.semanticRules.first()!!.head.name
    }

    /**
     * @return the name of the new instantiated semantics rule
     */
    private fun traverse(node: AttributeValue): String {
        when (node) {
            is AList -> {
                val op = node.entries.first()!! as AString
                val rule = rtgHelper.operatorMapping[op.value] ?: throw IllegalArgumentException("no such operator! $op")
                val childrenSemanticRuleNames = node.entries.drop(1).map { v -> traverse(v) } // drop the ctor, and traverse the rest
                val oldRuleName = rule.production.semanticRules.first()!!.head.name
                val newRuleName = "$oldRuleName$$semanticCounter"
                for (sem in rule.production.semanticRules) {
                    val childVarMap = sem.childTermVars.mapIndexed { index, v -> Pair(v.name, index) }.toMap()
                    val newInstRule = InstantiatedSemanticRule(
                        head = RelationApp(newRuleName, sem.head.arguments.filter { v -> v.type.name != rule.nonTerminalName }),
                        bodyRelations = sem.bodyRelations.map { br ->
                            val childVar = br.arguments.find { x -> x.name in childVarMap }
                            return@map if (childVar != null) {
                                RelationApp(
                                    childrenSemanticRuleNames[childVarMap[childVar.name]!!],
                                    br.arguments.filter { v -> v.name !in childVarMap }
                                )
                            } else {
                                // assert: occurrence of current rule!
                                assert(br.name == oldRuleName)
                                val currentASTVar =
                                    sem.head.arguments.first { v -> v.type.name == rule.nonTerminalName }
                                assert(br.arguments.any { v ->
                                    v.type.toSExpressionType() == currentASTVar.type.toSExpressionType()
                                        && v.name == currentASTVar.name })
                                RelationApp(
                                    newRuleName,
                                    br.arguments.filter { v -> v.name != currentASTVar.name }
                                )
                            }
                        },
                        constraint = sem.constraint,
                        variables = sem.variables.filter{ (_, v) ->
                            sem.head.arguments
                                .find { x -> x.name == v.name && x.type.name == rule.nonTerminalName } == null
                        },
                        childTermVars = sem.childTermVars
                    )
                    instantiatedSemantics.add(newInstRule)
                }
                println("$semanticCounter -> ${node.toSExpression()}")
                semanticCounter++
                return newRuleName
            }
            is AString -> {
                val term = node.value
                val rule = rtgHelper.operatorMapping[term] ?: throw IllegalArgumentException("no such term! $term")
                assert(rule.production.childNonTerminals.isEmpty())
                val newRuleName = rule.production.semanticRules.first()!!.head.name + "$$semanticCounter"
                for (sem in rule.production.semanticRules) {
                    assert(sem.childTermVars.isEmpty())
                    assert(sem.bodyRelations.isEmpty())
                    val newInstRule = InstantiatedSemanticRule(
                        head = RelationApp(newRuleName, sem.head.arguments.filter { v -> v.type.name != rule.nonTerminalName }),
                        bodyRelations = listOf(),
                        constraint = sem.constraint,
                        variables = sem.variables.filter{ (_, v) ->
                            sem.head.arguments
                                .find { x -> x.name == v.name && x.type.name == rule.nonTerminalName } == null
                        },
                        childTermVars = sem.childTermVars
                    )
                    instantiatedSemantics.add(newInstRule)
                }
                println("$semanticCounter -> $node")
                semanticCounter++
                return newRuleName
            }
            else -> throw IllegalArgumentException("Malformed program! node should be AList / AString, but we found ${node.javaClass.canonicalName}")
        }
    }
}