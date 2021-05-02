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
            TCon("B", Seq(BoolCon)),
            IntCon
          )
        ) ->: (IntCon ->: TCon("B", Seq(IntCon))) ->: BoolCon
      ).pretty(),
      "A (B Bool) Int -> (Int -> B Int) -> Bool"
    )
