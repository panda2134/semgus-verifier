package org.semgus.verifier

import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.verifier.frontend.visitFile
import org.semgus.verifier.smt.toSExpression
import org.semgus.verifier.walk.ProgramWalker

fun main(args: Array<String>) {
    val target = visitFile("/home/panda2134/Documents/chc-verifier/max2-exp.sem.json")
    val walker = ProgramWalker(target.program, target.problem)

    val res = walker.traverseProgram()
    println("1. ")
    println(res.first.joinToString("\n"))
    println("2. ")
    println(res.second)
    println(target.problem.constraints)
}