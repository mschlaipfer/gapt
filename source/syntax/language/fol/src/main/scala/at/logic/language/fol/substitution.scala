/*
 * Wrapper function for substitutions in FOL.
 *
 **/

package at.logic.language.fol

import at.logic.language.lambda.{Substitution => SubstitutionLambda, LambdaExpression, Var}

class Substitution(val map: Map[FOLVar, FOLExpression]) {
  def apply(t: FOLExpression): FOLExpression = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[FOLExpression]
  }
  def apply(t: FOLFormula): FOLFormula = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[FOLFormula]
  }
}
object Substitution {
  def apply(subs: List[(FOLVar, FOLExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: FOLVar, expression: FOLExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[FOLVar, FOLExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}

