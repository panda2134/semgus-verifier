package org.semgus.verifier

import org.semgus.verifier.frontend.visitFile
import org.semgus.verifier.smt.SmtAdapter
import org.semgus.verifier.walk.ProgramWalker

fun main() {
    val target = visitFile("./benchmarks/mul-by-while.sl.json")
    val walker = ProgramWalker(target.program, target.problem)

    val (instantiatedRules, rootRuleName) = walker.traverseProgram()

    val gen = SmtAdapter(target, rootRuleName, instantiatedRules)
    val path = gen.generateSmtFile()
    println(path)
    println(gen.runZ3AndParseModel(path))
}

