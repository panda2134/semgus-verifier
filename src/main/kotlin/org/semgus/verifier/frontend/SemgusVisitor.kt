package org.semgus.verifier.frontend

import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString
import org.semgus.java.problem.ProblemGenerator
import org.semgus.java.problem.SemgusProblem
import java.io.File

data class VerificationTarget (val problem: SemgusProblem, val program: AList)

fun visitFile(filePath: String): VerificationTarget {
    val reader = File(filePath).bufferedReader()
    val problem = ProblemGenerator.parse(reader)
    val solution = problem.metadata["solution"]
        ?: throw IllegalArgumentException("SemGus file contains no given solution, thus not usable for verification")
    solution as AList
    assert(solution.entries.size == 1)
    val solutionForFirstTarget = solution.entries[0]!! as AList
    val firstTargetName = solutionForFirstTarget.entries.first()!! as AString
    val firstProgram = solutionForFirstTarget.entries[1]!! as AList
    assert(firstTargetName.value == problem.targetName)
    if (solutionForFirstTarget.entries.size > 2) {
        println("WARNING: more than 1 program provided for the target. Only verifying the first one.")
    }
    return VerificationTarget(problem, program = firstProgram)
}