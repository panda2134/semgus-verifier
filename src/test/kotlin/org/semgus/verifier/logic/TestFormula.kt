package org.semgus.verifier.logic

import org.junit.jupiter.api.Test
import org.semgus.java.`object`.AttributeValue.AList
import org.semgus.java.`object`.AttributeValue.AString
import kotlin.test.assertEquals

class TestFormula {
    @Test
    fun testParse0() {
        val res = parseFormulaFromAttributeValue(AList(
            listOf(
                AString("forall"),
                AList(listOf(
                    AList(listOf(
                        AString("a"), AString("Int")
                    )),
                    AList(listOf(
                        AString("b"), AString("Int")
                    ))
                )),
                AList(listOf(
                    AString("=>"),
                    AList(listOf(
                        AString("="),
                        AString("a"),
                        AString("b")
                    )),
                    AList(listOf(
                        AString("="),
                        AString("a"),
                        AString("b")
                    ))
                ))
            )
        )).toSExpr()

        assertEquals("(forall ((a Int) (b Int)) (=> (= a b) (= a b)))", res)
    }
}