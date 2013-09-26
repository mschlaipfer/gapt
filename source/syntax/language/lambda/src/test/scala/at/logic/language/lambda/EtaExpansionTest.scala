package at.logic.language.lambda

import etaExpansion._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import typedLambdaCalculus._
import types.Definitions._
import symbols._
import types. {Ti, ->}

@RunWith(classOf[JUnitRunner])
class EtaExpansionTest extends SpecificationWithJUnit {
  val v = Var("v", i);
  val x = Var("x", i);
  val y = Var("y", i);
  val z = Var("z", i);
  val f = Var("f", i -> i);
  val g = Var("g", i -> i)
  val f2 = Var("f2", i -> i);
  val g2 = Var("g2", i -> i)
  val g3 = Var("g3", ->(Ti(),->(Ti(),Ti())))
  val g4 = Abs(x,g3)
  val g5 = Abs(x,App(g3,x))
  val g6 = Var("g6", ->(->(Ti(),Ti()),->(Ti(),Ti())))

  "EtaExpansion" should {
    "expand correctly the lambda expressions f : (i->i) to lambda x. f(x)" in {
      EtaExpand(f) must beEqualTo (Abs(x,App(f,x)))
    }
    "expand correctly the lambda expressions g3(x) : (i->i) to lambda y. g3(x,y)" in {
      EtaExpand(App(g3,x)) must beEqualTo (Abs(y, AppN(g3, x::y::Nil)))
    }
    "expand correctly the lambda expressions g3 : i->(i->i) to lambda x,y. g3(x,y)" in {
      EtaExpand(g3) must beEqualTo (AbsN(x::y::Nil, AppN(g3,x::y::Nil)))
    }
    "expand correctly the lambda expressions g3(g3(x,y)) : i to lambda z. g3(g3(x,y),z)" in {
      EtaExpand(App(g3, AppN(g3,x::y::Nil))) must beEqualTo (Abs(z, AppN(g3, AppN(g3, x::y::Nil)::z::Nil)))
    }
    "expand correctly the lambda expressions g6(f) : (i->i) to eta Abs(#7,App(App(g6, Abs(#8,App(f, #8))), #7))" in {
      EtaExpand(App(g6,f)) must beEqualTo (Abs(z,App(App(g6, Abs(x,App(f, x))), z)))
    }
    "expand correctly the lambda expressions g6 : (i->i)->(i->i) to lambda x,y. g6(lambda z. x(z),y)" in {
      EtaExpand(g6) must beEqualTo (AbsN(f::y::Nil, AppN(g6, Abs(z,App(f,z))::y::Nil)))
    }
    "expand correctly the lambda expressions f : (i->i) to f2 : (i->i)" in {
      val v2 = EtaExpand(Abs(x,App(g3,x)))
      EtaExpand(g3) must beEqualTo (v2)
    }
  }
}
