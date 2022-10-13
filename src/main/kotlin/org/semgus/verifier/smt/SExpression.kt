package org.semgus.verifier.smt

import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString
import org.semgus.java.`object`.RelationApp
import org.semgus.java.`object`.SmtTerm
import org.semgus.java.`object`.SmtTerm.Quantifier

fun AList.toSExpression(): String {
    return "(" + entries.joinToString(" ") { v ->
        when (v) {
            is AList -> v.toSExpression()
            is AString -> v.value
            else -> throw NotImplementedError("$v cannot be converted into S-expr")
        }
    } + ")"
}

fun RelationApp.toSExpression(argumentPrefix: String = ""): String {
    return "($name ${arguments.joinToString(" ") { v -> argumentPrefix + v.name }})"
}

fun Quantifier.Type.toSmtName(): String = when (this) {
    Quantifier.Type.FOR_ALL -> "forall"
    Quantifier.Type.EXISTS -> "exists"
    else -> throw IllegalArgumentException("cannot convert into smt name")
}

fun SmtTerm.toSExpression(): String =
    when (this) {
        is SmtTerm.Quantifier -> "(${type.toSmtName()}" +
                "(${bindings.joinToString(" ") { v -> "(${v.name} ${v.type})" }})" +
                child.toSExpression() + ")"
        is SmtTerm.Variable -> name
        is SmtTerm.Application ->
            if (arguments.isEmpty()) name.name
            else "($name ${arguments.joinToString(" ") { v -> v.term.toSExpression() }})"
        is SmtTerm.CString -> "\"${value}\""
        is SmtTerm.CNumber -> value.toString()
        is SmtTerm.CBitVector -> "#x" + value.toByteArray().reversed().joinToString { v -> "%02x".format(v) }
        else -> throw IllegalArgumentException("cannot convert this into s-expr")
    }