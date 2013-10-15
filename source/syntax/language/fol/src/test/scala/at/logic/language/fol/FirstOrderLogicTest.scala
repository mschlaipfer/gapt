/*
 * FirstOrderLogicTest.scala
 */

package at.logic.language.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._

@RunWith(classOf[JUnitRunner])
class FirstOrderLogicTest extends SpecificationWithJUnit {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val List( p, x,y,f,c ) = List("P","x","y","f","c")
      val Pc = FOLConst( p, (i -> (i -> (i -> o))) )
      val fc = FOLConst( f, (i -> i) )
      try {
      Atom( Pc, FOLVar(x)::Function(fc,FOLVar(y)::Nil)::FOLConst(c)::Nil ) must beLike {
        case FOLApp( FOLApp( FOLApp( Pc, FOLVar(x) ), FOLApp( fc, FOLVar(y) ) ), FOLConst(c) ) => ok
      }
      } catch {
        case e : Exception =>
          println(e.getMessage)
          e.printStackTrace
          ko
      }
    }
    "constructs correctly an atom using the factory" in {
      val var3 = Atom(FOLConst("X3", o), Nil)
      true
    }
    "constructs correctly an atom using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val tp = FunctionType(To(), args.map(a => a.exptype) )
      val atom1 = Atom(FOLConst("A", tp), args)
      val var3 = Atom(FOLConst("X3", o), Nil)
      val and1 = And(atom1, var3)
      true
    }
    "constructs correctly a forall using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val tp = FunctionType(To(), args.map(a => a.exptype) )
      val atom1 = Atom(FOLConst("A", tp),args)
      val all1 = AllVar(var1, atom1)
      true
    }

    "alpha equality as default provides that ∀x.∀x.P(x) is equal to ∀y.∀y.P(y)" in {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val p = FOLConst("P", ->(x.exptype, To()))
      val px = Atom(p,List(x))
      val py = Atom(p,List(y))
      val allall_px = AllVar(x, AllVar(x, px))
      val allall_py = AllVar(y, AllVar(y, py))

      allall_px must beEqualTo (allall_py)
    }
  }

  "First Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = FOLConst("P", Type("o"))
      val f = And(Atom(ps,Nil), Atom(ps,Nil))

      f must beLike {
        case Atom(_,_) => ko
        case AllVar(_,_) => ko
        case ExVar(_,_) => ko
        case Or(_,_) => ko
        case Imp(_,_) => ko
        case And(_,_) => ok
        case _ => ko
      }
    }
  }

}
