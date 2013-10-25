/*
 * ResolutionTest.scala
 *
 */

package at.logic.calculi.resolution

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.calculi.occurrences._
import at.logic.language.fol._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base._

import at.logic.language.hol.skolemSymbols.SkolemSymbolFactory

@RunWith(classOf[JUnitRunner])
class ResolutionTest extends SpecificationWithJUnit {
  
  "Paramodulation rule in Robinson Resolution" should {
    "be created correctly" in {
      val cl1 = InitialClause(Nil, Atom(FOLConst("=", Ti -> (Ti -> To)), Function(FOLConst("+", Ti -> (Ti -> Ti)), FOLVar("x")::FOLVar("x")::Nil)::FOLVar("x")::Nil)::Nil)
      val cl2 = InitialClause(Nil, Atom(FOLConst("=", Ti -> (Ti -> To)), Function(FOLConst("+", Ti -> (Ti -> Ti)), FOLVar("y")::FOLVar("y")::Nil)::FOLVar("y")::Nil)::Nil)
      val param = Paramodulation(cl1, cl2, cl1.root.succedent(0), cl2.root.succedent(0), Atom(FOLConst("=", Ti -> (Ti -> To)), FOLVar("y")::FOLVar("x")::Nil), Substitution(List((FOLVar("x"), FOLVar("y")))))
      val sq =  Seq(Atom(FOLConst("=", Ti -> (Ti -> To)), FOLVar("y")::FOLVar("y")::Nil))
      
      param.root.positive.map(_.formula) must beEqualTo (sq)
    }

    "correctly keep the context of demodulated formulas " in {
      val P = FOLConst("P", Ti -> To)
      val List(a,b,c,d,e,f) = List("a","b","c","d","e","f") map (x => FOLConst(x))
      val List(e1,e2,e3,p,q) = List(Equation(a,b), Equation(c,d), Equation(e,f), Atom(P,a::Nil), Atom(P,b::Nil)  )
      val p1 = InitialClause(Nil, List(e1, e2 ))
      val p2 = InitialClause(Nil, List(e3, p))
      val p3 = Paramodulation(p1,p2, p1.root.succedent(0), p2.root.succedent(1), q, Substitution())
      val expected_root = FSequent(Nil, List(e2,e3,q))

      p3.root.toFSequent must beSyntacticFSequentEqual(expected_root)

    }
  }
  "extrator on Resolution rule" should {
    "work properly" in {
      val x = FOLVar("x")
      val fa = Function(FOLConst("f", Ti -> Ti), List(FOLConst("a")))
      val Pfa = Atom(FOLConst("P", Ti -> To), List(fa))
      val Px = Atom(FOLConst("P", Ti -> To), List(x))
      val cl1 = InitialClause(List(), List(Px))
      val cl2 = InitialClause(List(Pfa), List())
      val res = Resolution(cl1, cl2, cl1.root.succedent(0), cl2.root.antecedent(0), Substitution(List((x,fa))))
      res must beLike { case Resolution(_,_,_,_,_,_) => ok }
    }
  }


 /* "Andrews Resolution" should {
    implicit val factory = PointerFOFactoryInstance

    "refute 'not (A or not A)'" in {
      val a = Atom(ConstantStringSymbol("p"), Nil)
      val s = Sequent(Nil, Neg(Or(a, Neg(a)))::Nil)
      val p0 = InitialSequent[SequentOccurrence](s)
      val p1 = NotT( p0, p0.root.succedent.head )
      val p2 = OrFL( p1, p1.root.antecedent.head )
      val p3 = OrFR( p1, p1.root.antecedent.head )
      val p4 = NotF( p3, p3.root.antecedent.head )
      val p5 = Cut( p4, p2, p4.root.succedent.head, p2.root.antecedent.head )
      p5.root.getSequent must beEqualTo(Sequent(Nil, Nil))
    }

    "handle strong quantifiers correctly" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val y = HOLVar(VariableStringSymbol("y"), i )
      val z = HOLVar(VariableStringSymbol("Z"), i -> o )
      val a = Atom(ConstantStringSymbol("R"), x::y::z::Nil)
      val qa = AllVar( x, a )

      qa.freeVariables must not contain( x )

      val sk = SkolemSymbolFactory.getSkolemSymbol

      // We do not care about the order of arguments. Do we?
      val skt1 = Function( sk, y::z::Nil, i -> o)
      val skt2 = Function( sk, z::y::Nil, i -> o)
      val ska1 = Atom(ConstantStringSymbol("R"), skt1::y::z::Nil )
      val ska2 = Atom(ConstantStringSymbol("R"), skt2::y::z::Nil )

      val p0 = InitialSequent[SequentOccurrence]( Sequent( qa::Nil, Nil ) )
      val p1 = ForallF( p0, p0.root.antecedent.head, sk )

      ska1::ska2::Nil must contain( p1.root.getSequent.antecedent.head )
    }

    "handle weak quantifiers and substitution correctly" in {
      val x = HOLVar(VariableStringSymbol("X"), i -> o )
      val f = HOLConst(ConstantStringSymbol("f"), (i -> o) -> i )
      val xfx = HOLApp(x, HOLApp( f, x ) ).asInstanceOf[HOLFormula]
      val m = AllVar( x, xfx )

      val z = HOLVar(VariableStringSymbol("z"), i)
      val Pz = Atom( ConstantStringSymbol("P"), z::Nil )
      val form = Or(Pz, Neg(Pz))
      val t = HOLAbs( z, form )

      val p0 = InitialSequent[SequentOccurrence]( Sequent( Nil, m::Nil ) )
      val p1 = ForallT( p0, p0.root.succedent.head, x )
      val p2 = Sub( p1, Substitution( x, t ) )

      val newa = Atom( ConstantStringSymbol("P"), HOLApp( f, t )::Nil )
      p2.root.getSequent.succedent.head must beEqualTo( 
        Or( newa, Neg( newa ) ) )
    }
  }      */
}
