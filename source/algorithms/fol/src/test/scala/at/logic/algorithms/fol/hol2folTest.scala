/*
 * hol2folTest.scala
 */

package at.logic.algorithms.fol.hol2fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.language.hol.{HOLVar, HOLConst, Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom}
import at.logic.language.hol.{ExVar => HOLExVar, AllVar => HOLAllVar, HOLExpression}
import at.logic.language.lambda.types._

import scala.collection.mutable

@RunWith(classOf[JUnitRunner])
class hol2folTest extends SpecificationWithJUnit {
  def imap = mutable.Map[HOLExpression, String]() // the scope for most tests is just the term itself
  def iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
  "HOL terms" should {
    val hx = HOLVar("x", Ti -> Ti)
    val ha = HOLConst("a", To -> Ti)
    val hb = HOLConst("b", To -> Ti)
    val fx = FOLVar("x")
    val fa = FOLConst("a")
    val fb = FOLConst("b")

    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        val hol = HOLAtom(HOLConst("A", (Ti -> Ti) -> ((To -> Ti) -> To)), hx::ha::Nil)
        val fol = Atom("A", fx::fa::Nil)
        reduceHolToFol(hol, imap, iid) must beEqualTo (fol)
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        val hol = HOLFunction(HOLConst("f", (Ti -> Ti) -> ((To -> Ti) -> (To -> To))), hx::ha::Nil)
        val fol = Function("f", fx::fa::Nil)
        reduceHolToFol(hol, imap, iid) must beEqualTo (fol)
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        val hA = HOLAtom(HOLConst("A", (Ti -> Ti) -> ((To -> Ti) -> To)), hx::ha::Nil)
        val hB = HOLAtom(HOLConst("B", (Ti -> Ti) -> ((To -> Ti) -> To)), hx::hb::Nil)
        val hol = HOLAnd(hA, hB)
        val fA = Atom("A", fx::fa::Nil)
        val fB = Atom("B", fx::fb::Nil)
        val fol = And(fA, fB)
        reduceHolToFol(hol, imap, iid) must beEqualTo (fol)
      }
      /* HOLAbs is no longer visible.
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("f(q_{1})").getTerm())
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("f(q_{1}(y))").getTerm())
      }
      "Two terms - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o) and g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" in {
        val map = mutable.Map[HOLExpression, String]()
        var id = new {var idd = 0; def nextId = {idd = idd+1; idd}}
        (reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm(),map,id)::
        reduceHolToFol(new MyParserHOL("g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)").getTerm(),map,id)::Nil) must beEqualTo(
        new MyParserFOL("f(q_{1}(y))").getTerm()::new MyParserFOL("g(q_{1}(z))").getTerm()::Nil)
      }
      */
    }
  }
}
