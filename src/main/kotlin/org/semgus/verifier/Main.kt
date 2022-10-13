package org.semgus.verifier

import org.semgus.java.`object`.SmtTerm.Application
import org.semgus.java.`object`.SmtTerm.Quantifier
import org.semgus.java.`object`.TypedVar
import org.semgus.verifier.frontend.visitFile
import org.semgus.verifier.smt.toSExpression
import org.semgus.verifier.walk.ProgramWalker

fun main(args: Array<String>) {
    val target = visitFile("./benchmarks/max2-exp.sl.json")
    val walker = ProgramWalker(target.program, target.problem)

    val (instantiatedRules, rootRuleName) = walker.traverseProgram()

    // only allow 1 constraint
    assert(target.problem.constraints.size == 1)
    val fullConstraint = target.problem.constraints.first() as Quantifier
    // only allow forall now
    assert(fullConstraint.type == Quantifier.Type.FOR_ALL)

    // inner parts of the quantified expression
    val quantifiedChild = fullConstraint.child as Application
    assert(quantifiedChild.name.name == "=>" && quantifiedChild.arguments.size == 2)
    val semOccurrence = quantifiedChild.arguments.first()!!.term as Application

    // extract the premise, which should be a semantic relation application
    val semRelationHead = target.problem.targetNonTerminal.productions.entries.first()
        .value.semanticRules.first()!!.head
    assert(semOccurrence.name.name == semRelationHead.name)
    val programArgPos = semRelationHead.arguments.indexOfFirst { v -> v.type.name == target.problem.targetNonTerminal.name }
    // ensure that the semantic relation is applied on the synthesis target
    assert((semOccurrence.arguments[programArgPos].term as Application).name.name == target.problem.targetName)

    val constraint = quantifiedChild.arguments.drop(1).first()
    println("; prelude")
    println("(set-logic HORN)")
    println()

    println("; relation declarations")
    println("(declare-rel Counterex (${fullConstraint.bindings.joinToString(" ") { v -> v.type.name }}))")
    val printedRules = mutableSetOf<String>()
    for (rule in instantiatedRules) {
        if (rule.head.name in printedRules) continue
        printedRules.add(rule.head.name)
        println("(declare-rel ${rule.head.name} (${rule.head.arguments.joinToString(" ") { v -> v.type.name }}))")
    }
    println()
    println("; semantic rules, instantiated with the given AST")
    for ((index, rule) in instantiatedRules.withIndex()) {
        val printed = mutableSetOf<String>()
        val printArgs = { xs: List<TypedVar> ->
            for (arg in xs) {
                val name = "$${index}$${arg.name}"
                if (name in printed) continue
                printed.add(name)
                println("(declare-var $name ${arg.type})")
            }
        }
        for (premise in rule.bodyRelations) {
            printArgs(premise.arguments)
        }
        printArgs(rule.head.arguments)
        println(rule.toSExpression("$${index}$"))
        println()
    }
    println()
    println("; verification condition")
    val rootRuleSExpr = "($rootRuleName ${semOccurrence.arguments
        .filter { v -> v.type.name != target.problem.targetNonTerminal.name }
        .joinToString(" ") { v -> v.term.toSExpression() }
    })"
    for (binding in fullConstraint.bindings) {
        println("(declare-var ${binding.name} ${binding.type})")
    }
    println("(rule (=> (and $rootRuleSExpr (not ${constraint.term.toSExpression()}))\n" +
            "          (Counterex ${fullConstraint.bindings.joinToString(" ") { v -> v.name }}) ))")
    println()
    println("; query for counterexamples")
    println("(query Counterex :print-certificate true)")
}