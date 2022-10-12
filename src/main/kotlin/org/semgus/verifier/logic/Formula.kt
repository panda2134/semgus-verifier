package org.semgus.verifier.logic

// TODO: refactor this; reuse code in Semgus-Parser

import org.semgus.java.`object`.AttributeValue
import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString
import java.lang.IllegalArgumentException
import java.text.Normalizer.Form

abstract class Formula (var parent: Formula?) {
    abstract fun toSExpr(): String
}

data class TypedVar (val varName: String, val varType: String)

/**
 * represents a variable or a constant
 */
class VariableExpression(val varName: String, parent: Formula? = null): Formula(parent) {
    override fun toSExpr(): String = varName
}

class UninterpretedFunctionExpression(val funcName: String, val arguments: List<Formula>, parent: Formula? = null):
    Formula(parent) {
    override fun toSExpr(): String = "(${funcName} ${arguments.joinToString(" ") { v -> v.toSExpr() }})"
    init {
        arguments.forEach { v -> v.parent = this }
    }
}

enum class LogicalConnection(val value: String) {
    AND("and"), OR("or"), NOT("not"), IMPLIES("=>"), EQUIV("=");
}

class LogicalConnectionExpression(val op: LogicalConnection, val children: List<Formula>, parent: Formula? = null): Formula(parent) {
    override fun toSExpr(): String = "(${op.value} ${children.map { x -> x.toSExpr() }.joinToString(" ")})"
    init {
        children.forEach { v -> v.parent = this }
    }
}

enum class Quantifier(val value: String) {
    FORALL("forall"), EXISTS("exists")
}

class QuantifiedFormula(val quantifier: Quantifier, val arguments: List<TypedVar>,
                        val child: Formula, parent: Formula? = null): Formula(parent) {
    override fun toSExpr(): String = "(${quantifier.value} " +
            "(${arguments.joinToString(" ") { v -> "(${v.varName} ${v.varType})" }}) " +
            "${child.toSExpr()})"
    init {
        child.parent = this
    }
}

fun parseFormulaFromAttributeValue(v: AttributeValue): Formula {
    when (v) {
        is AString -> {
            return VariableExpression(v.value)
        }
        is AList -> {
            val x = v.entries.first() as AString

            when (x.value) {
                "forall", "exists" -> {
                    // parsing quantifiers
                    val q = Quantifier.values().find { y -> x.value == y.value }!!
                    val argsExpr = v.entries.drop(1).first()
                    argsExpr is AList
                    val args = (argsExpr as AList).entries().map { kv ->
                        if (kv !is AList || kv.entries.size != 2
                            || kv.entries[0] !is AString || kv.entries[1] !is AString) {
                            throw IllegalStateException("invalid quantifier args")
                        }
                        TypedVar((kv.entries[0] as AString).value, (kv.entries[1] as AString).value)
                    }
                    val child = parseFormulaFromAttributeValue(v.entries.drop(2).first())
                    return QuantifiedFormula(q, args, child)
                }
                "and", "or", "not", "=>" -> {
                    // always treat = as non-boolean congruence currently
                    // we need a type-checker in the end
                    val children = v.entries.drop(1).map { t -> parseFormulaFromAttributeValue(t) }
                    val op = LogicalConnection.values().find { t -> t.value == x.value }!!
                    return LogicalConnectionExpression(op, children)
                }
                else -> {
                    // uninterpreted function
                    // we even treat = as uninterpreted
                    return UninterpretedFunctionExpression(x.value,
                        v.entries.drop(1).map { t -> parseFormulaFromAttributeValue(t) })
                }
            }
        }
        else -> throw IllegalArgumentException("cannot accept $v here")
    }
}