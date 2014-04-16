/*
 * hol2folTest.scala
 */

package at.logic.algorithms.fol.hol2fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

<<<<<<< .working
import at.logic.language.fol._
import at.logic.language.hol.{HOLVar, HOLConst, Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom}
import at.logic.language.hol.{ExVar => HOLExVar, AllVar => HOLAllVar, HOLExpression}
=======
import at.logic.language.fol
import at.logic.language.hol.{Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom, ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.hol.HOLVarFormula
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
>>>>>>> .merge-right.r1940
import at.logic.language.lambda.types._

import scala.collection.mutable
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.fol.FOLVar

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
        convertHolToFol(new MyParserHOL("A(x:i, a:i)").getTerm()) must beEqualTo (new MyParserFOL("A(x, a)").getTerm())
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        val hol = HOLFunction(HOLConst("f", (Ti -> Ti) -> ((To -> Ti) -> (To -> To))), hx::ha::Nil)
        val fol = Function("f", fx::fa::Nil)
        reduceHolToFol(hol, imap, iid) must beEqualTo (fol)
        convertHolToFol.convertTerm(new MyParserHOL("f(x:i, a:i):i").getTerm()) must beEqualTo (new MyParserFOL("f(x, a)").getTerm())
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        val hA = HOLAtom(HOLConst("A", (Ti -> Ti) -> ((To -> Ti) -> To)), hx::ha::Nil)
        val hB = HOLAtom(HOLConst("B", (Ti -> Ti) -> ((To -> Ti) -> To)), hx::hb::Nil)
        val hol = HOLAnd(hA, hB)
        val fA = Atom("A", fx::fa::Nil)
        val fB = Atom("B", fx::fb::Nil)
        val fol = And(fA, fB)
        reduceHolToFol(hol, imap, iid) must beEqualTo (fol)
        convertHolToFol(new MyParserHOL("And A(x:i, a:i) B(x:i, b:i)").getTerm()) must beEqualTo (new MyParserFOL("And A(x, a) B(x, b)").getTerm())
      }
      /* HOLAbs is no longer visible.
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("f(q_{1})").getTerm())
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        val red = reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm(),imap,iid)
        val fol = (new MyParserFOL("f(q_{1}(y))").getTerm())
        red must beEqualTo (fol)
      }
      "Two terms - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o) and g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" in {
<<<<<<< .working
        val map = mutable.Map[HOLExpression, String]()
=======
        println("two terms")
        val map = mutable.Map[LambdaExpression, ConstantStringSymbol]()
>>>>>>> .merge-right.r1940
        var id = new {var idd = 0; def nextId = {idd = idd+1; idd}}
<<<<<<< .working
        (reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm(),map,id)::
        reduceHolToFol(new MyParserHOL("g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)").getTerm(),map,id)::Nil) must beEqualTo(
        new MyParserFOL("f(q_{1}(y))").getTerm()::new MyParserFOL("g(q_{1}(z))").getTerm()::Nil)
=======
        val t1 = new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm()
        val t2 = new MyParserHOL("g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)").getTerm()
        val r1 = reduceHolToFol(t1,map,id)
        println("map="+map)
        val r2 = reduceHolToFol(t2,map,id)
        val s1 = new MyParserFOL("f(q_{1}(y))").getTerm()
        val s2 = new MyParserFOL("g(q_{1}(z))").getTerm()
        println(t1)
        println(t2)
        println(r1)
        println(r2)
        (r1::r2::Nil) must beEqualTo(s1::s2::Nil)
>>>>>>> .merge-right.r1940
      }
<<<<<<< .working
      */
=======
      "Correctly convert from type o to i on the termlevel" in {
        val List(sp,sq) = List("P","Q").map(ConstantStringSymbol)
        val List(x,y) = List("x","y").map(x => HOLVarFormula(VariableStringSymbol(x)))
        val f1 = HOLAtom(sp,List(HOLImp(x,y)))
        val f2 = fol.Atom(sp, List(fol.Function(ImpSymbol,
          List(fol.FOLConst(ConstantStringSymbol("x")),
               fol.FOLConst(ConstantStringSymbol("y"))))))
        val red = reduceHolToFol(f1)
        /*
        red match {
          case HOLAtom(_, List(HOLFunction(f,_,_))) =>
            println(f)
            //println(g)
          case _ => println("no match")
        }

        red must beEqualTo(f2)
        */
        //TODO: something in the conversion is still weird, fix it

      }
>>>>>>> .merge-right.r1940
    }
  }

  "Type replacement" should {
    "work for simple terms" in {
      val fterm1 = fol.Function(ConstantStringSymbol("f"), List(
        fol.FOLConst(ConstantStringSymbol("q_1")),
        fol.FOLConst(ConstantStringSymbol("c"))))

      val fterm2 = fol.AllVar(fol.FOLVar(VariableStringSymbol("x")),
                              fol.Atom(ConstantStringSymbol("P"),
                                       List(fol.FOLVar(VariableStringSymbol("q_1")),
                                            fol.FOLConst(ConstantStringSymbol("q_1"))) ))

      val hterm1 = changeTypeIn(fol2hol(fterm1), Map[String, TA](("q_1", Ti()->Ti()) ))
      val hterm2 = changeTypeIn(fol2hol(fterm2), Map[String, TA](("q_1", Ti()->Ti()) ))
      ok
    }
  }
}
