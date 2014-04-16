/*
 * hol.scala
 */

package at.logic.language.hol

import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.{LambdaExpression, FactoryA}

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

<<<<<<< .working
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
=======
  trait HOLExpression extends LambdaExpression with HOL {
    override def toString = this match {
      case Var(x,tpe) => x.toString + ":" + tpe.toString
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
      case Abs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
      case App(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    }
>>>>>>> .merge-right.r1940

<<<<<<< .working
=======
    //outer pretty printing, has no parenthesis around
    //TODO: introduce binding priorities and skip more parens
    def toPrettyString : String = this match {
      case Var(x,tpe) => x.toString
      case Atom(EqSymbol, List(left,right)) =>
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
      case Abs(v, exp) => "λ" + v.toString + "." + exp.toString
      case App(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    }
>>>>>>> .merge-right.r1940

<<<<<<< .working
}
=======
    //inner pretty printing, has parenthesis around
    def toPrettyString_ : String = this match {
      case Var(x,tpe) => x.toString
      case Atom(ConstantStringSymbol("="), List(left,right)) =>
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
      case Abs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
      case App(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    }
>>>>>>> .merge-right.r1940

<<<<<<< .working
// Should this be here?
trait Formula extends LambdaExpression {require(exptype == To)}
=======
    // ToDo: not sure if this is the best place for this method...
    def containsQuantifier : Boolean = this match {
      case Var(x,tpe) => false
      case Atom(x, args) => false
      // case Function(x, args, tpe) => x.containsQuantifier || args.exists(y => y.asInstanceOf[HOLExpression].containsQuantifier)  // I think this case is not really necessary, because it is covered by the last case...
      case And(x,y) => x.containsQuantifier || y.containsQuantifier
      case Or(x,y) => x.containsQuantifier || y.containsQuantifier
      case Imp(x,y) => x.containsQuantifier || y.containsQuantifier
      case Neg(x) => x.containsQuantifier
      case ExVar(x,f) => true
      case AllVar(x,f) => true
      case Abs(v, exp) => exp.asInstanceOf[HOLExpression].containsQuantifier
      case App(l, r) => l.asInstanceOf[HOLExpression].containsQuantifier || r.asInstanceOf[HOLExpression].containsQuantifier
    }
>>>>>>> .merge-right.r1940

trait HOLFormula extends HOLExpression with Formula

case object BottomC extends HOLConst(BottomSymbol, Type("o")) with HOLFormula
case object TopC extends HOLConst(TopSymbol, Type("o")) with HOLFormula
case object NegC extends HOLConst(NegSymbol, Type("(o -> o)"))
case object AndC extends HOLConst(AndSymbol, Type("(o -> (o -> o))"))
case object OrC extends HOLConst(OrSymbol, To -> (To -> To) )
case object ImpC extends HOLConst(ImpSymbol, Type("(o -> (o -> o))"))
// Synthetic connective to represent Herbrand Arrays
case object HArrayC extends HOLConst(HArraySymbol, Type("(o -> (o -> o))"))
case class EqC(e:TA) extends HOLConst(EqSymbol, ->(e, ->(e,"o")))

    // Returns the quantifier free part of a prenex formula
    def getMatrix : HOLFormula = {
      assert(this.isPrenex)
      this match {
        case Var(_,_) |
             Atom(_,_) |
             Imp(_,_) |
             And(_,_) |
             Or(_,_) |
             Neg(_) => this.asInstanceOf[HOLFormula]
        case ExVar(x,f0) => f0.getMatrix
        case AllVar(x,f0) => f0.getMatrix
        case _ => throw new Exception("ERROR: Unexpected case while extracting the matrix of a formula.")
      }
    }
// We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
object Neg {
  def apply(sub: HOLFormula) = {
    val neg = sub.factory.createConnective(NegSymbol).asInstanceOf[HOLConst]
    HOLApp(neg, sub).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(NegC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => TopC // No way to define from which layer this TopC comes from...
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )

    /**
     * the logical complexity of this formula, i.e. the number of logical connectives and atoms
     * starting from the root of the formula. The inner structure of atoms is not counted.
     **/
    def lcomp : Int = this match {
      case Atom(_, _) => 1
      case Neg(f) => f.lcomp + 1
      case And(f,g) => f.lcomp + g.lcomp + 1
      case Or(f,g) => f.lcomp + g.lcomp + 1
      case Imp(f,g) => f.lcomp + g.lcomp + 1
      case ExVar(x,f) => f.lcomp + 1
      case AllVar(x,f) => f.lcomp + 1
    }
  }
  def apply(left: HOLFormula, right: HOLFormula) = {
    val and = left.factory.createConnective(AndSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(and, left),right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(AndC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Or {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => BottomC // No way to define from which layer this BottomC comes from...
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }
  def apply(left: HOLFormula, right: HOLFormula) : HOLFormula = {
    val or = left.factory.createConnective(OrSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(or, left), right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(OrC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: HOLFormula, right: HOLFormula) = {
    val imp = left.factory.createConnective(ImpSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(imp, left), right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(ImpC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
  }
}

object Equation {
  def apply(left: HOLExpression, right: HOLExpression) = {
    require(left.exptype == right.exptype)
    val eq = left.factory.createConnective(EqSymbol, left.exptype).asInstanceOf[HOLConst]
    HOLApp(HOLApp(eq, left),right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(EqC(_),left),right) => Some( left.asInstanceOf[HOLExpression],right.asInstanceOf[HOLExpression] )
      case _ => None
  }
}

<<<<<<< .working
// Herbrand array definition
// TODO: this should die at some point... Herbrand sequents are subsumed by expansion trees
object HArray {
  def apply(left : HOLFormula, right: HOLFormula) = {
    HOLApp(HOLApp(HArrayC, left), right).asInstanceOf[HOLFormula]
=======
  case object BottomC extends HOLConst(BottomSymbol, "o") with HOLFormula
  case object TopC extends HOLConst(TopSymbol, "o") with HOLFormula
  case object NegC extends HOLConst(NegSymbol, "(o -> o)")
  case object AndC extends HOLConst(AndSymbol, "(o -> (o -> o))")
  case object OrC extends HOLConst(OrSymbol, "(o -> (o -> o))")
  case object ImpC extends HOLConst(ImpSymbol, "(o -> (o -> o))")
  class ExQ protected[hol](e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
  class AllQ protected[hol](e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))
  case class EqC(e:TA) extends HOLConst(EqSymbol, ->(e, ->(e,"o")))

  object HOLFactory extends LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int]) : Var =
      name match {
        case a: ConstantSymbolA =>
          if (isFormula(exptype)) new HOLConstFormula(a)
          else new HOLConst(a, exptype)
        case a: VariableSymbolA =>
          if (isFormula(exptype)) new HOLVarFormula(a,dbInd)
          else new HOLVar(a, exptype,dbInd)
      }

    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App =
      if (isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg)
      else new HOLApp(fun, arg)
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs  = new HOLAbs( variable, exp )
    def isFormula(typ: TA) = typ match {
      case To() => true
      case _ => false
    }
    def isFormulaWhenApplied(typ: TA) = typ match {
      case ->(in,To()) => true
      case _        => false
    }
>>>>>>> .merge-right.r1940
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
<<<<<<< .working
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : (HOLExpression, List[HOLExpression]) = e match {
    case v: HOLVar => (v, Nil)
    case c: HOLConst => (c, Nil)
    case HOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
=======

  object And {
    def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
      case Nil => TopC
      case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
    }
    def apply(left: HOLFormula, right: HOLFormula) = (App(App(AndC,left),right)).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(App(AndC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
    }
>>>>>>> .merge-right.r1940
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

<<<<<<< .working
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp(c: HOLConst,_) if isLogicalSymbol(c) => None
    case HOLApp(HOLApp(c: HOLConst,_),_) if isLogicalSymbol(c) => None
    case HOLApp(_,_) if (expression.exptype == To) => Some( unapply_(expression) )
    case HOLConst(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case HOLVar(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case _ => None
=======
  object Equation {
    def apply(left: HOLExpression, right: HOLExpression) = {
      require(left.exptype == right.exptype,
        "Can not create equation of "+left+" = "+right+". Reason: Types don't match!")
      App(App(EqC(left.exptype), left),right).asInstanceOf[HOLFormula]
    }
    def unapply(expression: LambdaExpression) = expression match {
        case App(App(EqC(_),left),right) => Some( left.asInstanceOf[HOLExpression],right.asInstanceOf[HOLExpression] )
        case _ => None
    }
>>>>>>> .merge-right.r1940
  }
<<<<<<< .working
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : (HOLExpression, List[HOLExpression]) = e match {
    case v: HOLVar => (v, Nil)
    case c: HOLConst => (c, Nil)
    case HOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

=======

>>>>>>> .merge-right.r1940
// TODO: Is it possible to simplify the quantifiers? There are too many objects for that...
private class ExQ(e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
private object ExQ {
  def apply(tp: TA) = new ExQ(tp)
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (HOLConst(_, t), ExistsSymbol) => Some(t)
    case _ => None
  }
}
private class AllQ(e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))
private object AllQ {
  def apply(tp: TA) = new AllQ(tp)
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (HOLConst(_, t), ForallSymbol) => Some(t)
    case _ => None
  }
}

<<<<<<< .working
private object Ex {
  def apply(sub: HOLExpression) = {
    val ex = sub.factory.createConnective(ExistsSymbol, sub.exptype).asInstanceOf[HOLConst]
    HOLApp(ex, sub).asInstanceOf[HOLFormula]
=======
  object ExQ {
    def unapply(v: Var) = v match {
      case vo: ExQ => Some(vo.exptype)
      case _ => None
    }
>>>>>>> .merge-right.r1940
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

private object All {
  def apply(sub: HOLExpression) = {
    val all = sub.factory.createConnective(ForallSymbol, sub.exptype).asInstanceOf[HOLConst]
    HOLApp(all, sub).asInstanceOf[HOLFormula]
  }
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


