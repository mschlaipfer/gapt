/*
 * BetaReduction.scala
 *
 */

package at.logic.language.lambda

import symbols._

/* The BetaReduction object encapsulates two functions:
 * 1) betaNormalize, which transforms a lambda expression to beta normal form.
 * 2) betaReduce, which applies only one rewrite step to a lambda expression.
 *
 * These functions take additional arguments specifying which strategy should
 * be used for reduction. The chosen strategies determine which redex is
 * selected for reduction first. The strategy options are implemented as
 * an Enumeration and are:
 * 1) Outermost (call-by-name) or Innermost (call-by-value)
 * 2) Leftmost or Rightmost [these are only relevant for betaReduce]
 *
 * In principle, betaNormalize could have been implemented as a while loop
 * iterating betaReduce. However, for efficiency reasons, this has not been done.
 *
 */
object BetaReduction {

  class ReductionException(msg: String) extends Exception(msg)
  
  abstract class Strategy extends Enumeration
  object StrategyOuterInner extends Strategy {
    val Outermost = Value
    val Innermost = Value
  }
  object StrategyLeftRight extends Strategy {
    val Leftmost = Value
    val Rightmost = Value
  }

  object ImplicitStandardStrategy {
    implicit val implicitOuter = StrategyOuterInner.Outermost
    implicit val implicitLeft = StrategyLeftRight.Leftmost
  }

  def betaNormalize[T <: LambdaExpression](expression: T)(implicit strategy: StrategyOuterInner.Value) : T = expression match {
    case App(Abs(x, body), arg) => strategy match {
      // If it is outermost strategy, we first reduce the current redex by applying sigma, and then we call betaNormalize recursively on the result.
      case StrategyOuterInner.Outermost => 
        val sigma = Substitution(x, arg)
        betaNormalize(sigma(body)).asInstanceOf[T]
      case StrategyOuterInner.Innermost => 
        val sigma = Substitution(x, betaNormalize(arg))
        sigma(betaNormalize(body)).asInstanceOf[T]
    }
    case App(m,n) => 
      val mnorm = betaNormalize(m)
      mnorm match {
        case _: Abs => betaNormalize(expression.factory.createApp(mnorm,betaNormalize(n))).asInstanceOf[T]
        case _ => expression.factory.createApp(mnorm,betaNormalize(n)).asInstanceOf[T]
      }
    case Abs(x,m) => expression.factory.createAbs(x,betaNormalize(m)).asInstanceOf[T]
    case x: Var => x.asInstanceOf[T]
    case x: Cons => x.asInstanceOf[T]
  }

  def betaReduce[T <: LambdaExpression](expression: T)(implicit strategyOI: StrategyOuterInner.Value, strategyLR: StrategyLeftRight.Value): T = expression match {
    
    case App(Abs(x, t),arg) => strategyOI match {
      
      case StrategyOuterInner.Outermost => 
        val sigma = Substitution(x, arg)
        sigma(t).asInstanceOf[T]
      
      case StrategyOuterInner.Innermost => strategyLR match {
        
        case StrategyLeftRight.Rightmost => 
          val argr = betaReduce(arg)(strategyOI,strategyLR)   // Since it is innerrightmost redex strategy, we try first to reduce the argument.
          if (argr != arg) expression.factory.createApp(expression.factory.createAbs(x, t), argr).asInstanceOf[T]               // If it succeeds, great!
          else {                                              // If it doesn't, then we try to find an innermost redex in the left side, i.e. in the body.
            val bodyr = betaReduce(t)(strategyOI,strategyLR)
            if (bodyr != t) expression.factory.createApp(expression.factory.createAbs(x, bodyr), arg).asInstanceOf[T]           // If it succeeds, great!
            else {
              val sigma = Substitution(x, arg)
              sigma(t).asInstanceOf[T]
            }
          }

        case StrategyLeftRight.Leftmost =>                     // Analogous to the previous case, but giving priority to the left side (body) instead of the ride side (arg)
          val bodyr = betaReduce(t)(strategyOI,strategyLR)
          if (bodyr != t) expression.factory.createApp(expression.factory.createAbs(x, bodyr), arg).asInstanceOf[T]
          else {
            val argr = betaReduce(arg)(strategyOI,strategyLR)
            if (argr != arg) expression.factory.createApp(expression.factory.createAbs(x, t), argr).asInstanceOf[T]
            else {
              val sigma = Substitution(x, arg)
              sigma(t).asInstanceOf[T]
            }
          }
      }
    }

    case App(m,n) => strategyLR match {
      case StrategyLeftRight.Leftmost => {
        val mr = betaReduce(m)(strategyOI,strategyLR)        // Since it is leftmost redex strategy, we try first to reduce the left side (m).
        if (mr != m) expression.factory.createApp(mr,n).asInstanceOf[T]                               // If it succeeds, great!
        else expression.factory.createApp(m, betaReduce(n)(strategyOI,strategyLR)).asInstanceOf[T]    // If it doesn't, then we try to find and reduce a redex in the right side (n)
      }
      case StrategyLeftRight.Rightmost => {
        val nr = betaReduce(n)(strategyOI,strategyLR)        // Since it is rightmost redex strategy, we try first to reduce the right side (n).
        if (nr != n) expression.factory.createApp(m,nr).asInstanceOf[T]                               // If it succeeds, great!
        else expression.factory.createApp(betaReduce(m)(strategyOI,strategyLR), n ).asInstanceOf[T]   // If it doesn't, then we try to find and reduce a redex in the left side (m)
      }
    }

    case Abs(x,m) => expression.factory.createAbs(x,betaReduce(m)(strategyOI,strategyLR)).asInstanceOf[T]
    case x: Var => x.asInstanceOf[T]
  }
}
