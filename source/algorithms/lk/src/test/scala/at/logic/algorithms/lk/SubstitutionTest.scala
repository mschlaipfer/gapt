
package at.logic.algorithms.lk

import at.logic.language.hol._
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk._
import at.logic.language.lambda.types._

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    "apply correctly to a simple proof" in {
      val x = HOLVar( "x", Ti )
      val p = HOLConst("P", Ti -> To)
      val px = Atom(p, x::Nil )
      val s = FSequent( px::Nil, px::Nil )
      val ax1 = Axiom( px::Nil, px::Nil )
      val ax2 = Axiom( px::Nil, px::Nil )
      val proof = CutRule( ax1, ax2, ax1.root.succedent.toList.head, ax2.root.antecedent.toList.head )
      val a = HOLConst("a", Ti)
      val f = HOLConst("f", Ti -> Ti)
      val fa = HOLApp(f, a)
      val subst = Substitution( x, fa )
      val p_s = applySubstitution( proof, subst )
      val pfa = Atom(p, fa::Nil )
      val new_seq = FSequent( pfa::Nil, pfa::Nil )
      val seq = p_s._1.root.toFSequent
      seq must beEqualTo( new_seq )
    }
  }
}
