/*
 * sQMONparserTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, NegLeftRule, Axiom}
import at.logic.calculi.lksk.Axiom
import at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class sFOparserTest extends SpecificationWithJUnit {
  private class MyParser extends StringReader("")

  sequential
  "sFOparser" should {

    "parse correctly a FO SLK-proof" in {
      val var3 = HOLVarFormula(new VariableStringSymbol("x3"))
      val var4 = HOLVarFormula(new VariableStringSymbol("x4"))
      val ax1  = at.logic.calculi.lk.propositionalRules.Axiom(var3::Nil, var3::Nil)
      val ax2  = at.logic.calculi.lk.propositionalRules.Axiom(var4::Nil, var4::Nil)
      val negl = NegLeftRule(ax1, var3)
      val proof  = OrLeftRule(negl, ax2, var3, var4)


      val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
      val i = IntVar(new VariableStringSymbol("i"))
      val Ai2 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(i)))
      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
      val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
      val ax11 = at.logic.calculi.lk.propositionalRules.Axiom(A0::Nil, A0::Nil)

      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sIND.lks"))

      val map = sFOParser.parseProof(s)

      def f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
      def h = HOLConst(new ConstantStringSymbol("h"), ->(Tindex() , ->(Ti(), Ti())))
      def g = HOLConst(new ConstantStringSymbol("g"), ->(Tindex() , ->(Ti(), Ti())))
      val k = IntVar(new VariableStringSymbol("k"))
      val x = foVar("x")//hol.createVar(new VariableStringSymbol("x"), Ti(), None).asInstanceOf[HOLVar]
      val base2 = x
      val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val base1 = sTerm(g, IntZero(), x::Nil)
      val step1 = sTerm(g, Succ(k), x::Nil)
      dbTRS.clear
      dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))
      val varphi = applySchemaSubstitution2("\\sigma",2)
      // specs2 require a least one Result, see org.specs2.specification.Example
      Success()

    }


    "parse correctly the journal example" in {
      //println(Console.RED+"\n---- applySchemaSubstitution ----\n"+Console.RESET)

      val var3 = HOLVarFormula(new VariableStringSymbol("x3"))
      val var4 = HOLVarFormula(new VariableStringSymbol("x4"))
      val ax1  = at.logic.calculi.lk.propositionalRules.Axiom(var3::Nil, var3::Nil)
      val ax2  = at.logic.calculi.lk.propositionalRules.Axiom(var4::Nil, var4::Nil)
      val negl = NegLeftRule(ax1, var3)
      val proof  = OrLeftRule(negl, ax2, var3, var4)

      val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
      val i = IntVar(new VariableStringSymbol("i"))
      val Ai2 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(i)))
      val Ai = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
      val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
      val ax11 = at.logic.calculi.lk.propositionalRules.Axiom(A0::Nil, A0::Nil)

      val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))

      val map = sFOParser.parseProof(s)

      def f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
      def h = HOLConst(new ConstantStringSymbol("h"), ->(Tindex() , ->(Ti(), Ti())))
      def g = HOLConst(new ConstantStringSymbol("g"), ->(Tindex() , ->(Ti(), Ti())))
      val k = IntVar(new VariableStringSymbol("k"))
      val x = foVar("x")//hol.createVar(new VariableStringSymbol("x"), Ti(), None).asInstanceOf[HOLVar]
      val base2 = x
      val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val base1 = sTerm(g, IntZero(), x::Nil)
      val step1 = sTerm(g, Succ(k), x::Nil)
      dbTRS.clear
      dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))
      val sigma = applySchemaSubstitution2("\\varphi",3)

      Success()

    }
  }
}


