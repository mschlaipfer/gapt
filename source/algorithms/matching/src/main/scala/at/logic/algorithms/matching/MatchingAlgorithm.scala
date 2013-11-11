/*
 * MatchingAlgorithm.scala
 *
 */

//Commenting this out because it refers to lambda Var and Substitution. If we want
//to implement this interface, the layers would be mixed up. [Giselle]

package at.logic.algorithms.matching

import at.logic.language.lambda._

// the restrictedDomain is a list of variables that should not be included in the substitution.
// i.e. these are variables contained on the right hand side of an object (clause, sequent, etc.) that contains the lambda expression to be matched
trait MatchingAlgorithm[T <: LambdaExpression] {
  def matchTerm(term: T, posInstance: T, restrictedDomain: List[Var]): Option[Substitution]
}
