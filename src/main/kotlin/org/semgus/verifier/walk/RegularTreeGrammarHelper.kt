package org.semgus.verifier.walk

import org.semgus.java.problem.SemgusNonTerminal
import org.semgus.java.problem.SemgusProduction

class RegularTreeGrammarHelper(nonTerminals: Map<String, SemgusNonTerminal>) {
    data class ProductionRule(val operator: String, val nonTerminalName: String, val production: SemgusProduction)
    val operatorMapping = nonTerminals.values.flatMap { nt ->
        nt.productions.values.map { p ->
            ProductionRule(operator = p.operator, nonTerminalName = nt.name, production = p)
        }
    }.associateBy { v -> v.operator }
}