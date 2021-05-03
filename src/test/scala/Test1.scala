import org.junit.Test
import org.junit.Assert.*

import Typ.*

class Test1:
  @Test def test_prettyPrintedTypes(): Unit =
    assertEquals(
      (
        TCon(
          "A",
          Seq(
            TCon("B", Seq(boolCon)),
            intCon
          )
        ) ->: (intCon ->: TCon("B", Seq(intCon))) ->: boolCon
      ).pretty(),
      "A (B Bool) Int -> (Int -> B Int) -> Bool"
    )

  @Test def test_recursiveFactorial(): Unit =
    val src = raw"""
      let fact =
        rec f = \x.\y. if is_zero x then y else f (pred x) (mult x y)
        in \x. f x 1
      in fact 10
    """
    val expr = Parser.parseAll(Parser.program, src) match
      case Parser.Success(matched, _) => matched
      case _ => throw Exception(s"parser failure")
    assertEquals(expr.typecheck.toString, "Int")
