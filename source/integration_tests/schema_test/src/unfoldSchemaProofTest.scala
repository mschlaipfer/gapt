
package at.logic.algorithms.shlk

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import java.io.{FileInputStream, InputStreamReader}
import java.io.File.separator
//import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
//import at.logic.language.lambda.symbols.ImplicitConverters._
//import at.logic.calculi.occurrences._
//import at.logic.calculi.lk.base.Sequent
//import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr}
//import at.logic.calculi.lk.macroRules._
//import at.logic.calculi.slk._
//import at.logic.calculi.lk.base.types.FSequent
//import at.logic.language.lambda.symbols._
//import at.logic.language.hol.logicSymbols._
//import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
//import at.logic.language.lambda.typedLambdaCalculus._
//import at.logic.language.lambda.types._
//import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.schema._
//import at.logic.calculi.lksk.{Axiom => LKskAxiom,
//WeakeningLeftRule => LKskWeakeningLeftRule,
//WeakeningRightRule => LKskWeakeningRightRule,
//ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}
//import at.logic.calculi.lk.propositionalRules._
//import at.logic.calculi.lk.quantificationRules._
//import at.logic.calculi.lk.equationalRules._
//import at.logic.calculi.lk.definitionRules._
//import at.logic.parsing.readers.StringReader
//import org.specs2.execute.Success

// Moved this test to integration_tests because it uses an external file.
@RunWith(classOf[JUnitRunner])
class UnfoldSchemaProofTest extends SpecificationWithJUnit {
    //implicit val factory = defaultFormulaOccurrenceFactory
    "UnfoldSchemaProofTest" should {
      "unfold the adder.slk" in {
        val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
        val str = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "adder.lks"))
        val map = SHLK.parseProof(str)
        val n = IntVar(new VariableStringSymbol("n"));val n1 = Succ(n);val n2 = Succ(n1);val n3 = Succ(n2);
        val k = IntVar(new VariableStringSymbol("k")) ; val i = IntVar(new VariableStringSymbol("i"))
        val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)
        val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
        val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
        val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
        val b = BigAnd(i, A, zero, n3)
        val subst = Substitution((k, two)::Nil)

        Success()
      }
    }
 }

