package org.semgus.verifier.smt

import org.semgus.java.`object`.AttributeValue
import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString

fun AList.toSExpression(): String {
    return "(" + entries.joinToString(" ") { v ->
        when (v) {
            is AList -> v.toSExpression()
            is AString -> v.value
            else -> throw NotImplementedError("$v cannot be converted into S-expr")
        }
    } + ")"
}