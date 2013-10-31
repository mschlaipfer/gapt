/*
 * hol.scala
 */

package at.logic.language.hol

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.{LambdaExpression, Var, Const, App, Abs, FactoryA}
import at.logic.language.lambda.types._

trait HOLExpression extends LambdaExpression {

  // Factory for App, Abs and Var
  override def factory : FactoryA = HOLFactory
  
  // How many toString methods does one need??
  override def toString = this match {
    case HOLVar(x,tpe) => x.toString + ":" + tpe.toString
    case HOLConst(x,tpe) => x.toString + ":" + tpe.toString
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + "): o"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + "):" + tpe.toString
    case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
    case Equation(x,y) => "(" + x.toString + EqSymbol + y.toString + ")"
    case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
    case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
    case Neg(x) => NegSymbol + x.toString
    case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
    case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
    case HArray(f1, f2) => "(" + f1.toString + HArraySymbol + f2.toString + ")"
    case HOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }

  //outer pretty printing, has no parenthesis around
  //TODO: introduce binding priorities and skip more parens
  def toPrettyString : String = this match {
    case HOLVar(x,tpe) => x.toString
    case HOLConst(x,tpe) => x.toString
    case Atom(c: HOLConst, List(left,right)) if c.sym == EqSymbol =>
      left.toPrettyString_ + " "+ EqSymbol + " " + right.toPrettyString_
    case Atom(x, args) =>
      x + "(" +
      (if (args.size > 1) args.head.toPrettyString_ + args.tail.foldLeft("")((s,a) => s+", "+a.toPrettyString_)
      else args.foldLeft("")((s,a) => s+a.toPrettyString_)) + ")"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toPrettyString_)
      else args.foldLeft("")((s,a) => s+a.toPrettyString_)) + ")"
    case And(x,y) => x.toPrettyString_ + AndSymbol + y.toPrettyString_
    case Equation(x,y) => x.toPrettyString_ + EqSymbol + y.toPrettyString_
    case Or(x,y) => x.toPrettyString_ + OrSymbol + y.toPrettyString_
    case Imp(x,y) => x.toPrettyString_ + ImpSymbol + y.toPrettyString_
    case Neg(x) => NegSymbol + x.toPrettyString_
    case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toPrettyString_
    case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toPrettyString_
    case HArray(f1, f2) =>  f1.toPrettyString_ + HArraySymbol + f2.toPrettyString_
    case HOLAbs(v, exp) => "λ" + v.toString + "." + exp.toString
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }

  //inner pretty printing, has parenthesis around
  def toPrettyString_ : String = this match {
    case HOLVar(x,tpe) => x.toString
    case HOLConst(x,tpe) => x.toString
    case Atom(c: HOLConst, List(left,right)) if c.sym == EqSymbol =>
      left.toPrettyString_ + " = " + right.toPrettyString_
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toPrettyString_ + args.tail.foldLeft("")((s,a) => s+", "+a.toPrettyString_)
      else args.foldLeft("")((s,a) => s+a.toPrettyString_)) + ")"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toPrettyString_)
      else args.foldLeft("")((s,a) => s+a.toPrettyString_)) + ")"
    case And(x,y) => "(" + x.toPrettyString_ + AndSymbol + y.toPrettyString_ + ")"
    case Equation(x,y) => "(" + x.toPrettyString_ + EqSymbol + y.toPrettyString_ + ")"
    case Or(x,y) => "(" + x.toPrettyString_ + OrSymbol + y.toPrettyString_ + ")"
    case Imp(x,y) => "(" + x.toPrettyString_ + ImpSymbol + y.toPrettyString_ + ")"
    case Neg(x) => NegSymbol + x.toPrettyString_
    case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toPrettyString_
    case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toPrettyString_
    case HArray(f1, f2) => "(" + f1.toPrettyString_ + HArraySymbol + f2.toPrettyString_ + ")"
    case HOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }


}

// Should this be here?
trait Formula extends LambdaExpression {require(exptype == To)}

trait HOLFormula extends HOLExpression with Formula

class HOLVar protected[hol] (sym: SymbolA, exptype: TA) extends Var(sym, exptype) with HOLExpression 
object HOLVar {
  def apply(name: String, exptype: TA) : HOLVar = HOLVar(StringSymbol(name), exptype)
  // If it is a formula, use the constructor for HOLVarFormula
  def apply(sym: SymbolA, exptype: TA) : HOLVar = exptype match {
    case To => new HOLVar(sym, exptype) with HOLFormula
    case _ => new HOLVar(sym, exptype)
  }
  def unapply(exp: HOLExpression) = exp match {
    case v: HOLVar => Some( (v.name, v.exptype) )
    case _ => None
  }
}

class HOLConst protected[hol] (sym: SymbolA, exptype: TA) extends Const(sym, exptype) with HOLExpression
object HOLConst {
  def apply(name: String, exptype: TA) : HOLConst = HOLConst(StringSymbol(name), exptype)
  // If it is a formula, use the constructor for HOLConstFormula
  def apply(sym: SymbolA, exptype: TA) : HOLConst = exptype match {
    case To => new HOLConst(sym, exptype) with HOLFormula
    case _ => new HOLConst(sym, exptype)
  }
  def apply(name: String, exptype: String) : HOLConst = HOLConst(name, Type(exptype))
  def unapply(exp: HOLExpression) = exp match {
    case c: HOLConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

class HOLApp protected[hol] (function: HOLExpression, arg: HOLExpression) extends App(function, arg) with HOLExpression
object HOLApp {
  // If it is a formula, use the constructor for HOLAppFormula
  def apply(function: HOLExpression, argument: HOLExpression) = function.exptype match {
    case ->(_, To) => new HOLApp(function, argument) with HOLFormula
    case _ => new HOLApp(function, argument)
  }
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
  def apply(variable: HOLVar, expression: HOLExpression) = new HOLAbs(variable, expression)
  def unapply(exp: HOLExpression) = exp match {
    case a: HOLAbs => Some( (a.variable.asInstanceOf[HOLVar], a.term.asInstanceOf[HOLExpression]) )
    case _ => None
  }
}

case object BottomC extends HOLConst(BottomSymbol, Type("o")) with HOLFormula
case object TopC extends HOLConst(TopSymbol, Type("o")) with HOLFormula
case object NegC extends HOLConst(NegSymbol, Type("(o -> o)"))
case object AndC extends HOLConst(AndSymbol, Type("(o -> (o -> o))"))
case object OrC extends HOLConst(OrSymbol, Type("(o -> (o -> o))"))
case object ImpC extends HOLConst(ImpSymbol, Type("(o -> (o -> o))"))
// Synthetic connective to represent Herbrand Arrays
case object HArrayC extends HOLConst(HArraySymbol, Type("(o -> (o -> o))"))
class ExQ protected[hol](e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
class AllQ protected[hol](e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))
case class EqC(e:TA) extends HOLConst(EqSymbol, ->(e, ->(e,"o")))


// We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
object Neg {
  def apply(sub: HOLFormula) = HOLApp(NegC,sub).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(NegC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => BottomC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
  def apply(left: HOLFormula, right: HOLFormula) = (HOLApp(HOLApp(AndC,left),right)).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(AndC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Or {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => BottomC
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }
  def apply(left: HOLFormula, right: HOLFormula) : HOLFormula = HOLApp(HOLApp(OrC,left),right).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(OrC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: HOLFormula, right: HOLFormula) = HOLApp(HOLApp(ImpC,left),right).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(ImpC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
  }
}

object Equation {
  def apply(left: HOLExpression, right: HOLExpression) = {
    require(left.exptype == right.exptype)
    HOLApp(HOLApp(EqC(left.exptype), left),right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(EqC(_),left),right) => Some( left.asInstanceOf[HOLExpression],right.asInstanceOf[HOLExpression] )
      case _ => None
  }
}

// Herbrand array definition
object HArray {
  def apply(left : HOLFormula, right: HOLFormula) = {
    HOLApp(HOLApp(HArrayC, left), right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(HArrayC, left), right) => Some(left.asInstanceOf[HOLFormula], right.asInstanceOf[HOLFormula])
    case _ => None
  }
}

object Function {
  def apply(head: HOLVar, args: List[HOLExpression]): HOLExpression = apply_(head, args)
  def apply(head: HOLConst, args: List[HOLExpression]): HOLExpression = apply_(head, args)

  private def apply_(head: HOLExpression, args: List[HOLExpression]): HOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(HOLApp(head, t), tl)
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp(c: HOLConst,_) if isLogicalSymbol(c) => None
    case HOLApp(HOLApp(c: HOLConst,_),_) if isLogicalSymbol(c) => None
    case HOLApp(_,_) if (expression.exptype != To) => 
      val t = unapply_(expression) 
      Some( (t._1, t._2, expression.exptype) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : (HOLExpression, List[HOLExpression]) = e match {
    case v: HOLVar => (v, Nil)
    case c: HOLConst => (c, Nil)
    case HOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

// HOL formulas of the form P(t_1,...,t_n)
object Atom {
  def apply(head: HOLVar, args: List[HOLExpression]): HOLFormula = apply_(head, args).asInstanceOf[HOLFormula]
  def apply(head: HOLVar): HOLFormula = head.asInstanceOf[HOLFormula]
  def apply(head: HOLConst, args: List[HOLExpression]): HOLFormula = apply_(head, args).asInstanceOf[HOLFormula]
  def apply(head: HOLConst): HOLFormula = head.asInstanceOf[HOLFormula]

  private def apply_(head: HOLExpression, args: List[HOLExpression]): HOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(HOLApp(head, t), tl)
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp(c: HOLConst,_) if isLogicalSymbol(c) => None
    case HOLApp(HOLApp(c: HOLConst,_),_) if isLogicalSymbol(c) => None
    case HOLApp(_,_) if (expression.exptype == To) => Some( unapply_(expression) )
    case HOLConst(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case HOLVar(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : (HOLExpression, List[HOLExpression]) = e match {
    case v: HOLVar => (v, Nil)
    case c: HOLConst => (c, Nil)
    case HOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

// TODO: Is it possible to simplify the quantifiers? There are too many objects for that...
object ExQ {
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (vo@HOLConst(_, t), ExistsSymbol) => Some(t)
    case _ => None
  }
}
object AllQ {
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (vo@HOLConst(_, t), ForallSymbol) => Some(t)
    case _ => None
  }
}

object Ex {
  def apply(sub: HOLExpression) = HOLApp(new ExQ(sub.exptype),sub).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object All {
  def apply(sub: HOLExpression) = HOLApp(new AllQ(sub.exptype),sub).asInstanceOf[HOLFormula]
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(AllQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object ExVar {
  def apply(variable: HOLVar, sub: HOLFormula) = Ex(HOLAbs(variable, sub))
  def unapply(expression: HOLExpression) = expression match {
    case Ex(HOLAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: HOLVar, sub: HOLFormula) = All(HOLAbs(variable, sub))
  def unapply(expression: HOLExpression) = expression match {
    case All(HOLAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Quantifier {
  def unapply(expression: HOLExpression) = expression match {
    case ExVar(x, f) => Some(ExistsSymbol, x, f)
    case AllVar(x, f) => Some(ForallSymbol, x, f)
    case _ => None
  }
}

/*********************** Factories *****************************/

object HOLFactory extends FactoryA {
  def createVar(name: String, exptype: TA) : HOLVar = HOLVar(name, exptype)
  def createConst(name: String, exptype: TA) : HOLConst = HOLConst(name, exptype)
  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : HOLApp = HOLApp(fun.asInstanceOf[HOLExpression], arg.asInstanceOf[HOLExpression])
  def createAbs( variable: Var, exp: LambdaExpression ) : HOLAbs  = HOLAbs( variable.asInstanceOf[HOLVar], exp.asInstanceOf[HOLExpression] )
}

