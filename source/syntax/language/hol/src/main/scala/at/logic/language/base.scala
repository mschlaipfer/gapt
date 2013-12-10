/*
 *
 * HOL's mini lambda-calculus and factory
 *
 */

package at.logic.language.hol

import at.logic.language.lambda.{LambdaExpression, Var, Const, App, Abs, FactoryA}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._
import scala.Some

class HOLVar protected[hol] (sym: SymbolA, exptype: TA) extends Var(sym, exptype) with HOLExpression 
object HOLVar {
  def apply(name: String, exptype: TA) : HOLVar = HOLFactory.createVar(StringSymbol(name), exptype)
  def apply(sym: SymbolA, exptype: TA) : HOLVar = HOLFactory.createVar(sym, exptype)
  def unapply(exp: HOLExpression) = exp match {
    case v: HOLVar => Some( (v.name, v.exptype) )
    case _ => None
  }
}

class HOLConst protected[hol] (sym: SymbolA, exptype: TA) extends Const(sym, exptype) with HOLExpression
object HOLConst {
  def apply(name: String, exptype: TA) : HOLConst = HOLFactory.createConst(StringSymbol(name), exptype)
  def apply(sym: SymbolA, exptype: TA) : HOLConst = HOLFactory.createConst(sym, exptype)
  def apply(name: String, exptype: String) : HOLConst = HOLFactory.createConst(StringSymbol(name), Type(exptype))
  def unapply(exp: HOLExpression) = exp match {
    case c: HOLConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

class HOLApp protected[hol] (function: HOLExpression, arg: HOLExpression) extends App(function, arg) with HOLExpression
object HOLApp {
  def apply(function: HOLExpression, argument: HOLExpression) : HOLApp = argument.factory.createApp(function, argument).asInstanceOf[HOLApp] 
  def apply(function: HOLExpression, arguments: List[HOLExpression]) : HOLExpression = arguments match {
    case Nil => function
    case h :: tl => apply(HOLApp(function, h), tl)
  }
  def unapply(exp: HOLExpression) = exp match {
    case a: HOLApp => Some( ( a.function.asInstanceOf[HOLExpression], a.arg.asInstanceOf[HOLExpression] ) )
    case _ => None
  }
}

class HOLAbs protected[hol] (variable: HOLVar, term: HOLExpression) extends Abs(variable, term) with HOLExpression
object HOLAbs {
  def apply(variable: HOLVar, expression: HOLExpression) : HOLAbs = expression.factory.createAbs(variable, expression).asInstanceOf[HOLAbs]
  def unapply(exp: HOLExpression) = exp match {
    case a: HOLAbs => Some( (a.variable.asInstanceOf[HOLVar], a.term.asInstanceOf[HOLExpression]) )
    case _ => None
  }
}

/*********************** Factory *****************************/

object HOLFactory extends FactoryA {
  def createVar(sym: SymbolA, exptype: TA) : HOLVar = exptype match {
    case To => new HOLVar(sym, exptype) with HOLFormula
    case _ => new HOLVar(sym, exptype)
  }
  def createConst(sym: SymbolA, exptype: TA) : HOLConst = (sym, exptype) match {
    case (TopSymbol, To) => TopC
    case (BottomSymbol, To) => BottomC
    case (NegSymbol, Ti -> To) => NegC
    case (AndSymbol, Ti -> (Ti -> To)) => AndC
    case (OrSymbol,  Ti -> (Ti -> To)) => OrC
    case (ImpSymbol, Ti -> (Ti -> To)) => ImpC
    case (EqSymbol, t1 -> (t2 -> To)) =>
      require(t1 == t2, "Creating an equation needs both sides to be of the same type, not "+t1+" and "+t2)
      EqC(t1)
    case (ForallSymbol, t1 -> To) => new AllQ(t1)
    case (ExistsSymbol, t1 -> To) => new ExQ(t1)
    case (sym : LogicalSymbolA, _ ) =>
      throw new Exception("Trying to create an unrecognized logical constant in HOL : "+sym+" of type " + exptype)
    case (_,To) => new HOLConst(sym, exptype) with HOLFormula
    case _ => new HOLConst(sym, exptype)
  }
  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : HOLApp = fun.exptype match {
    case ->(_, To) => new HOLApp(fun.asInstanceOf[HOLExpression], arg.asInstanceOf[HOLExpression]) with HOLFormula
    case _ => new HOLApp(fun.asInstanceOf[HOLExpression], arg.asInstanceOf[HOLExpression])
  }
  def createAbs( variable: Var, exp: LambdaExpression ) : HOLAbs  = new HOLAbs( variable.asInstanceOf[HOLVar], exp.asInstanceOf[HOLExpression] )
}

