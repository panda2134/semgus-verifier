package org.semgus.verifier.smt

import org.semgus.verifier.walk.ProgramWalker

class SMTGenerator(val rootSemanticsName: String,
                   val instantiatedSemanticRules: List<ProgramWalker.InstantiatedSemanticRule>
                   ) {
    val prelude = """
        (set-logic HORN)
        (set-option :fp.engine spacer)
        (set-option :fp.xform.slice false)
        (set-option :fp.xform.inline_linear false)
        (set-option :fp.xform.inline_eager false)
        (set-option :parallel.enable true)
    """.trimIndent()


}