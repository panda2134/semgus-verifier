package org.semgus.verifier

import org.semgus.verifier.frontend.visitFile
import org.semgus.verifier.smt.SmtAdapter
import org.semgus.verifier.walk.ProgramWalker

fun main() {
    val target = visitFile("./benchmarks/plus-2-times-3/wrong.sl.json")
    val walker = ProgramWalker(target.program, target.problem)

    val (instantiatedRules, rootRuleName) = walker.traverseProgram()

    val gen = SmtAdapter(target, rootRuleName, instantiatedRules)
    val pathList = gen.generateSmtFile()
    println(pathList)

    for ((i, path) in pathList.withIndex()) {
        print("File $i: ")
        val (verified, model) = gen.runZ3AndParseModel(path)
        val modelStr: String? = model?.joinToString(", ") { v -> "${v.first.name}=${v.second}" }
        println("$verified $modelStr")
        if (!verified) {
            println("[COUNTEREX] $modelStr")
            return
        }
    }
    println("[VERIFIED] no counterexamples")
}

