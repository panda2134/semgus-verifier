package org.semgus.verifier.smt

import org.semgus.java.`object`.SmtTerm
import org.semgus.java.`object`.SmtTerm.Application
import org.semgus.java.`object`.SmtTerm.Quantifier
import org.semgus.java.`object`.SmtTerm.Variable
import org.semgus.java.`object`.TypedVar

fun SmtTerm.withVariablePrefix(prefix: String): SmtTerm =
    when (this) {
        is SmtTerm.Application ->
            Application(
                name,
                returnType,
                arguments.map { v -> Application.TypedTerm(v.type, v.term.withVariablePrefix(prefix)) }
            )

        is SmtTerm.Variable ->
            Variable(
                prefix + name,
                type
            )

        is SmtTerm.Quantifier -> {
            Quantifier(
                type,
                bindings.map { v -> TypedVar(prefix + v.name, v.type) },
                child.withVariablePrefix(prefix)
            )
        }
        is SmtTerm.CBitVector, is SmtTerm.CNumber, is SmtTerm.CString -> this
        else -> throw IllegalStateException("cannot add prefix to this!")
    }
