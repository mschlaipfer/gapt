/*
 * Wrapper function for beta-reduction in HOL.
 *
 **/

package at.logic.language.hol

import at.logic.language.lambda.{BetaReduction => BetaReductionLambda}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

object BetaReduction {

  def betaNormalize(expression: HOLExpression) : HOLExpression = 
    BetaReductionLambda.betaNormalize(expression).asInstanceOf[HOLExpression]

  def betaReduce(expression: HOLExpression) : HOLExpression = 
    BetaReductionLambda.betaReduce(expression).asInstanceOf[HOLExpression]
}
