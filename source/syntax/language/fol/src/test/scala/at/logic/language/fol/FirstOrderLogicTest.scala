/*
 * FirstOrderLogicTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.fol

//import at.logic.language.hol.replacements.Replacement
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda._

@RunWith(classOf[JUnitRunner])
class FirstOrderLogicTest extends SpecificationWithJUnit {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val List( p, x,y,f,c ) = List("P","x","y","f","c")
      val Pc = FOLFactory.createCons( p, (i -> (i -> (i -> o))) )
      val fc = FOLFactory.createCons( f, (i -> o) )
      try {
      Atom( p, FOLVar(x)::Function(f,FOLVar(y)::Nil)::FOLConst(c)::Nil ) must beLike {
        case App( App( App( Pc, FOLVar(x) ), App( fc, FOLVar(y) ) ), FOLConst(c) ) => ok
      }
      } catch {
        case e : Exception =>
          println(e.getMessage)
          e.printStackTrace
          ko
      }
    }
    "constructs correctly an atom using the factory" in {
      val var3 = Atom("X3", Nil)
      true
    }
    "constructs correctly an atom using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val atom1 = Atom("A",var1::var2::const1::Nil)
      val var3 = Atom("X3", Nil)
      val and1 = And(atom1, var3)
      true
    }
    "constructs correctly a forall using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val atom1 = Atom("A",var1::var2::const1::Nil)
      val all1 = AllVar(var1, atom1)
      true
    }

    "alpha equality as default provides that ∀x.∀x.P(x) is equal to ∀y.∀y.P(y)" in {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val p = "P"
      val px = Atom(p,List(x))
      val py = Atom(p,List(y))
      val allall_px = AllVar(x, AllVar(x, px))
      val allall_py = AllVar(y, AllVar(y, py))

      allall_px must beEqualTo (allall_py)
    }

    /*
    "Replacement on first order terms" in {
        Replacement(List(),Function( "∩", FOLVar( "x_{0}" )::FOLVar( "x_{0}" )::Nil)).apply(Atom( "=" , Function( ConstantStringSymbol( "∩" ), FOLVar( VariableStringSymbol( "x_{2}" ) )::FOLVar( VariableStringSymbol( "x_{1}" ) )::Nil)::Function( ConstantStringSymbol( "∩" ), FOLVar( VariableStringSymbol( "x_{1}" ) )::FOLVar( VariableStringSymbol( "x_{2}" ) )::Nil)::Nil)) must beEqualTo (Function( ConstantStringSymbol( "∩" ), FOLVar( VariableStringSymbol( "x_{0}" ) )::FOLVar( VariableStringSymbol( "x_{0}" ) )::Nil))
    } */


  }

  "First Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = "P"
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
