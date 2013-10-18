/*
 * macroRules.scala
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.ds.trees._
import base._

  /** <pre>Replaces a formulas A, B (marked by term1oc & term2oc) with the conjunction
    * A ^ B in the antecedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *     sL, A, B |- sR
    * ------------------- (AndLeft)
    * sL, A ^ B |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, A, B |- sR) as the bottommost sequent.
    * @param term1oc The occurrence of A in the antecedent of s1.
    * @param term2oc The occurrence of B in the antecedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
object AndLeftRule {
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val p0 = AndLeft1Rule( s1, term1oc, term2oc.formula.asInstanceOf[HOLFormula] )
    val p1 = AndLeft2Rule( p0, term1oc.formula.asInstanceOf[HOLFormula], p0.getDescendantInLowerSequent( term2oc ).get )
    ContractionLeftRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
  }

  /** <pre>Replaces a formulas term1, term2 with the conjunction
    * term1 ^ term2 in the antecedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    * sL, term1, term2 |- sR
    * ---------------------- (AndLeft)
    * sL, term1 ^ term2 |- sR
    * </pre>
    * 
    * @param s1 The top proof with (sL, term1, term2 |- sR) as the bottommost sequent.
    * @param term1 The first formula to be replaced in the antecedent of s1.
    * @param term2 The second formula to be replaced in the antecedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val x1 = s1.root.antecedent.find( _.formula == term1 )
    if (x1 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    val x2 = s1.root.antecedent.find( x => x.formula == term2 && x != x1.get )
    if (x2 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    apply(s1, x1.get, x2.get)
  }
}

object OrRightRule {

  /** <pre>Replaces a formulas A, B (marked by term1oc & term2oc) with the disjunction
    * A v B in the succedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    *   sL|- sR, A, B
    * ------------------- (OrRight)
    * sL |- sR, A v B
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, A, B) as the bottommost sequent.
    * @param term1oc The occurrence of A in the succedent of s1.
    * @param term2oc The occurrence of B in the succedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
    val p0 = OrRight1Rule( s1, term1oc, term2oc.formula )
    val p1 = OrRight2Rule( p0, term1oc.formula, p0.getDescendantInLowerSequent( term2oc ).get )
    ContractionRightRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
  }

  /** <pre>Replaces a formulas term1, term2 with the disjunction
    * term1 v term2 in the succedent of a sequent. 
    * 
    * The rule: 
    *     (rest of s1)
    * sL |- sR, term1, term2
    * ---------------------- (OrRight)
    * sL |- sR, term1 v term2
    * </pre>
    * 
    * @param s1 The top proof with (sL |- sR, term1, term2) as the bottommost sequent.
    * @param term1 The first formula to be replaced in the succedent of s1.
    * @param term2 The second formula to be replaced in the succedent of s2.
    * @return An LK Proof ending with the new inference.
    */ 
  def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
    val x1 = s1.root.succedent.find( _.formula == term1 )
    if (x1 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    val x2 = s1.root.succedent.find( x => x.formula == term2 && x != x1.get )
    if (x2 == None)
      throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
    apply(s1, x1.get, x2.get)
  }
}

