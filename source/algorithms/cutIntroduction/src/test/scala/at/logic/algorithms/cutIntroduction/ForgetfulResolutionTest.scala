/*
* Tests for forgetful resolution.
*
*/

package at.logic.algorithms.cutIntroduction

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import CutIntroduction._

@RunWith(classOf[JUnitRunner])
class ForgetfulResolutionTest extends SpecificationWithJUnit {

  "Forgetful Resolution Should" should {

    "compute a single resolvent successfully" in {
      val a = Atom("A")
      val b = Atom("B")
      val c = Atom("C")
      val d = Atom("D")
      val e = Atom("E")

      val f = And(And(Or(a,Or(b,c)), Or(Neg(b), d)), e)

      val res = ForgetfulResolve(f)

      //println("Formula (in CNF): " + f)
      //println("Resolvent: " + res)

      res.size must beEqualTo(1)
    }

/*
    "improve the solution correctly" in {
      val p = at.logic.testing.LinearExampleProof(8)
      val ts = new FlatTermSet(TermsExtraction(p))
      val g = ComputeGrammars(ts)
      val grm = g(2)
      val ehs = new ExtendedHerbrandSequent(p.root, grm, ts)
      val improv = improveSolution(ehs.canonicalSol, ehs)

      // TODO: type the expected value correctly
      //val expected =
      //improv must
      success
    }
*/
  }
}

