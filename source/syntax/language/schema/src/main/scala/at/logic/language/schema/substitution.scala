/*
 * Wrapper function for substitutions in Schema.
 *
 **/

package at.logic.language.schema

import at.logic.language.lambda.{Substitution => SubstitutionLambda, LambdaExpression, Var}

class Substitution(val map: Map[SchemaVar, SchemaExpression]) {
  def apply(t: SchemaExpression): SchemaExpression = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[SchemaExpression]
  }
  def apply(t: SchemaFormula): SchemaFormula = {
    val s = SubstitutionLambda(map.asInstanceOf[Map[Var, LambdaExpression]])
    s(t).asInstanceOf[SchemaFormula]
  }
}
object Substitution {
  def apply(subs: List[(SchemaVar, SchemaExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: SchemaVar, expression: SchemaExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[SchemaVar, SchemaExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}

