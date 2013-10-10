/*
 * LambdaCalculusTest.scala
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import types._
import symbols._
import types.Definitions._
import scala.math.signum

@RunWith(classOf[JUnitRunner])
class LambdaCalculusTest extends SpecificationWithJUnit {
  
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {
      (Var("p",i) ) must beEqualTo (Var("p", i ))
    }
    "create N-ary abstractions (AbsN) correctly" in {
      val v1 = Var("x",i)
      val v2 = Var("y",i)
      val f = Var("f",i -> (i -> o))
      ( Abs(v1::v2::Nil, f) match {
        case Abs(v1,Abs(v2,f)) => true
        case _ => false
        }) must beEqualTo ( true )
    }
    "create N-ary applications (AppN) correctly" in {
      val v1 = Var("x",i)
      val v2 = Var("y",i)
      val f = Var("f",i -> (i -> o))
      ( App(f, List(v1,v2)) match {
        case App(App(f, v1), v2) => true
        case _ => false
        }) must beEqualTo ( true )
    }
  }
  
  "Equality" should {
    "work correctly for alpha conversion" in {
      val a1 = Abs(Var("y", Ti()), App(Var("x",i->i), Var("y", Ti())))
      val b1 = Abs(Var("z", Ti()), App(Var("x",i->i), Var("z", Ti())))
      "- (\\y.xy) = (\\z.xz)" in {
        (a1) must beEqualTo (b1)
      }
      val a2 = Abs(Var("y", Ti()), a1)
      val b2 = Abs(Var("w", Ti()), a1)
      "- (\\y.\\y.xy) = (\\w.\\y.xy)" in {
        (a2) must beEqualTo (b2)
      }
      val a3 = Abs(Var("y", Ti()), App(Abs(Var("y", Ti()), Var("x", Ti())), Var("y", Ti())))
      val b3 = Abs(Var("w", Ti()), App(Abs(Var("y", Ti()), Var("x", Ti())), Var("w", Ti())))
      "- (\\y.(\\y.x)y) = (\\w.(\\y.x)w)" in {
        (a3) must beEqualTo (b3)
      }
      val a4 = Abs(Var("y", Ti()), App(Abs(Var("y", Ti()), Var("x", Ti())), Var("y", Ti())))
      val b4 = Abs(Var("y", Ti()), App(Abs(Var("y", Ti()), Var("x", Ti())), Var("w", Ti())))
      "- (\\y.(\\y.x)y) != (\\y.(\\y.x)w)" in {
        (a4) must not be equalTo (b4)
      }
      val a5 = Abs(Var("y", Ti()), App(Abs(Var("y", Ti()), Var("y", Ti())), Var("y", Ti())))
      val b5 = Abs(Var("y", Ti()), App(Abs(Var("w", Ti()), Var("w", Ti())), Var("y", Ti())))
      "- (\\y.(\\y.y)y) = (\\y.(\\w.w)y)" in {
        (a5) must beEqualTo (b5)
      }
      val a6 = Abs(Var("y", Ti()), App(Abs(Var("y", Ti()), Var("y", Ti())), Var("y", Ti())))
      val b6 = Abs(Var("y", Ti()), App(Abs(Var("w", Ti()), Var("y", Ti())), Var("x", Ti())))
      "- (\\y.(\\y.y)y) != (\\y.(\\w.y)y)" in {
        (a6) must not be equalTo (b6)
      }
    }
  }

  "extract free variables correctly" in {
      val x = Var("X", i -> o )
      val y = Var("y", i )
      val z = Var("Z", i -> o )
      val r = Var("R", (i -> o) -> (i -> ((i -> o) -> o)))
      val a = App(r, x::y::z::Nil)
      val qa = Abs( x, a )
      val free = qa.freeVariables
      free must not (have( _.syntaxEquals(x) ))
      free must have (_.syntaxEquals(y) )
      free must have (_.syntaxEquals(z) )
      free must have (_.syntaxEquals(r) )
  }

  "deal correctly with bound variables in the Abs extractor" in {
    val x = Var("x", i)
    val p = Var("p", i -> o)
    val px = App(p, x)
    val xpx = Abs(x, px)

    val res = xpx match {
      case Abs(v, t) => Abs(v, t)
    }

    res must beEqualTo( xpx )
  }
}
