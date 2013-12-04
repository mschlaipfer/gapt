/*
 * StillmanSubsumptionAlgorithm.scala
 *
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching._
import at.logic.language.hol.{HOLExpression, Substitution => SubstitutionHOL, Neg => NegHOL, HOLVar, freeVariables => freeVariablesHOL}
import at.logic.language.fol.{FOLFormula, FOLExpression, Substitution => SubstitutionFOL, Neg => NegFOL, FOLVar, freeVariables => freeVariablesFOL}
import at.logic.calculi.lk.base.FSequent

object StillmanSubsumptionAlgorithmHOL extends SubsumptionAlgorithm {
  val matchAlg = NaiveIncompleteMatchingAlgorithm
  def subsumes(s1: FSequent, s2: FSequent): Boolean =
    // TODO: what is the second map doing????
    ST(s1._1.map(x => NegHOL(x)) ++ s1._2.map(x => x),
      s2._1.map(x => NegHOL(x)) ++ s2._2.map(x => x), 
      SubstitutionHOL(), 
      (s2._1.flatMap(x => freeVariablesHOL(x)) ++ s2._2.flatMap(x => freeVariablesHOL(x))).toList)

  def ST(ls1: Seq[HOLExpression], ls2: Seq[HOLExpression], sub: SubstitutionHOL, restrictedDomain: List[HOLVar]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
  }
}

object StillmanSubsumptionAlgorithmFOL extends SubsumptionAlgorithm {
  val matchAlg = FOLMatchingAlgorithm
  def subsumes(s1: FSequent, s2: FSequent): Boolean =
    ST(s1._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s1._2.map(x => x.asInstanceOf[FOLFormula]),
      s2._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s2._2.map(x => x.asInstanceOf[FOLFormula]), 
      SubstitutionFOL(), 
      (s2._1.flatMap(x => freeVariablesFOL(x.asInstanceOf[FOLFormula])) ++ s2._2.flatMap(x => freeVariablesFOL(x.asInstanceOf[FOLFormula]))).toList)

  def ST(ls1: Seq[FOLExpression], ls2: Seq[FOLExpression], sub: SubstitutionFOL, restrictedDomain: List[FOLVar]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
  }
}
