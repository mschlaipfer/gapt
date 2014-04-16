/*
 * fol.scala
 */

package at.logic.language.fol

import at.logic.language.lambda.FactoryA
import at.logic.language.hol.{HOLExpression, HOLFormula, isLogicalSymbol}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._

/**
 *The following is a note about the construction of this trait. Right now FOLExpression refers to both valid FOL terms
 * and formulas and components of such valid terms and formulas, so for example, the head symbol of an atom is also a
 * fol expression although it has a complex type.
 * @author ?
 * @version ?
 */
/* TODO we need to separate fol expression into FOLExpression which refers  only to valid fol expressions and to
FOLComponent which contains the fol factory but refers to possibly invalid fol expressions.
 */

trait FOLExpression extends HOLExpression {
  /**
   * This function takes a FOL construction and converts it to a string version. The String version is made
   * by replacing the code construction for logic symbols by string   versions in the file language/hol/logicSymbols.scala.
   * Terms are also handled by the this function.
   *
   @param  this  The method has no parameters other then the object which is to be written as a string
   *
   @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
   *
   */
  override def toString = this match {
    case FOLVar(x) => x.toString
    case FOLConst(x) => x.toString
    case FOLLambdaConst(x, t) => x + ": " + t.toString
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + ")"
    case Function(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + ")"
    case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
    case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
    case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
    case Neg(x) => NegSymbol + x.toString
    case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
    case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
    case FOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case FOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => 
      val r = super.toString
      throw new Exception("toString: expression is not FOL: " + r)
    }

<<<<<<< .working
    override def factory : FactoryA = FOLFactory
=======
  /**
   * This is an identity function for FOL construction, in that this
   *function takes a FOL statement, and outputs the statement as it was written/coded. Old
   *comment for this function was written as follows:
   * this function outputs the string which creates
   * an object like this. can be used to create
   * tests based on bugs.
   *
   The method has no parameters other then the object which is to be written as a string
   @param  this  The method has no parameters other then the object which is to be written as a string
   *
   @return A String illustrating the construction of the given FOL expression
   *
   */
    def toCode : String = this match {
      case FOLVar(x) => "FOLVar( " + x.toCode + " )"
      case FOLConst(x) => "FOLConst( " + x.toCode + " )"
      case Atom(x, args) => "Atom( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case Function(x, args) => "Function( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case And(x,y) => "And(" + x.toCode + ", " + y.toCode + ")"
      case Or(x,y) => "Or(" + x.toCode + ", " + y.toCode + ")"
      case Imp(x,y) => "Imp(" + x.toCode + ", " + y.toCode + ")"
      case Neg(x) => "Neg(" + x.toCode + ")"
      case ExVar(x,f) => "ExVar(" + x.toCode + ", " + f.toCode + ")"
      case AllVar(x,f) => "AllVar(" + x.toCode + ", " + f.toCode + ")"
    }
  }
>>>>>>> .merge-right.r1940

}

trait FOLFormula extends FOLExpression with HOLFormula

trait FOLTerm extends FOLExpression { require( exptype == Ti ) }

case object TopC extends FOLLambdaConst(TopSymbol, To) with FOLFormula
case object BottomC extends FOLLambdaConst(BottomSymbol, To) with FOLFormula
case object NegC extends FOLLambdaConst(NegSymbol, To -> To )
case object AndC extends FOLLambdaConst(AndSymbol, To -> (To -> To))
case object OrC extends FOLLambdaConst(OrSymbol,   To -> (To -> To))
case object ImpC extends FOLLambdaConst(ImpSymbol, To -> (To -> To))
case object EqC extends FOLLambdaConst(EqSymbol,   Ti -> (Ti -> To))

object Equation {
  def apply(left: FOLTerm, right: FOLTerm) = {
    val eq = left.factory.createConnective(EqSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(eq, left),right).asInstanceOf[FOLFormula]
  }
<<<<<<< .working
  def unapply(expression: FOLExpression) = expression match {
      case FOLApp(FOLApp(EqC,left),right) => Some( left.asInstanceOf[FOLTerm],right.asInstanceOf[FOLTerm] )
      case _ => None
=======

  // Distribute Ors over Ands
  def distribute : FOLFormula = this match {
    case Atom(_,_) => this
    //case Function(_,_) => this
    // Negation has only atomic scope
    case Neg(Atom(_,_)) => this
    //case Neg(Function(_,_)) => this
    case And(f1, f2) => And(f1.distribute, f2.distribute)
    case Or(f1, And(f2,f3)) => And(Or(f1,f2).distribute, Or(f1,f3).distribute)
    case Or(And(f1,f2), f3) => And(Or(f1,f3).distribute, Or(f2,f3).distribute)
    case Or(f1, f2) => Or(f1.distribute, f2.distribute)
    case _ => {
      throw new Exception("ERROR: Unexpected case while distributing Ors over Ands.")
    }
>>>>>>> .merge-right.r1940
  }
<<<<<<< .working
=======

  // Transforms a formula to conjunctive normal form
  // 1. Transform to negation normal form
  // 2. Distribute Ors over Ands
  // OBS: works for propositional formulas only
  // TODO: tests for this
  def toCNF : FOLFormula = this.toNNF.distribute

  def numOfAtoms : Int = this match {
    case Atom(_,_) => 1
    case Function(_,_) => 1
    case Imp(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case And(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case Or(f1,f2) => f1.numOfAtoms + f2.numOfAtoms
    case ExVar(x,f) => f.numOfAtoms
    case AllVar(x,f) => f.numOfAtoms
    case Neg(f) => f.numOfAtoms
    case _ => throw new Exception("ERROR: Unexpected case while counting the number of atoms.")
  }
>>>>>>> .merge-right.r1940
}

// FOL atom of the form P(t_1,...,t_n)
object Atom {
  def apply(head: String, args: List[FOLTerm]): FOLFormula = {
    val tp = FunctionType(To, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLFormula]
  }
  def apply(head: String): FOLFormula = FOLLambdaConst(head, To).asInstanceOf[FOLFormula]
  def apply(head: SymbolA, args: List[FOLTerm]): FOLFormula = {
    val tp = FunctionType(To, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLFormula]
  }
  def apply(head: SymbolA): FOLFormula = FOLLambdaConst(head, To).asInstanceOf[FOLFormula]
  
  private def apply_(head: FOLExpression, args: List[FOLTerm]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLLambdaConst,_) if isLogicalSymbol(c) => None
    case FOLApp(FOLApp(c: FOLLambdaConst,_),_) if isLogicalSymbol(c) => None
    case FOLApp(_,_) if (expression.exptype == To) => Some( unapply_(expression) )
    case c: FOLLambdaConst if (c.exptype == To) => Some( (c.sym, Nil) )
    case v: FOLVar if (v.exptype == To) => Some( (v.sym, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (SymbolA, List[FOLTerm]) = e match {
    //case v: FOLVar => (v.sym, Nil)
    case c: FOLLambdaConst => (c.sym, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2.asInstanceOf[FOLTerm])
  }
}

// FOL function of the form f(t_1,...,t_n)
object Function {  

  def apply(head: String, args: List[FOLTerm]): FOLTerm = {
    val tp = FunctionType(Ti, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLTerm]
  }
  def apply(head: SymbolA, args: List[FOLTerm]): FOLTerm = {
    val tp = FunctionType(Ti, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLTerm]
  }
  
  private def apply_(head: FOLExpression, args: List[FOLTerm]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLLambdaConst,_) if isLogicalSymbol(c) => None
    case FOLApp(FOLApp(c: FOLLambdaConst,_),_) if isLogicalSymbol(c) => None
    case FOLApp(_,_) if (expression.exptype != To) => 
      val t = unapply_(expression) 
      Some( (t._1, t._2) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (SymbolA, List[FOLTerm]) = e match {
    case c: FOLLambdaConst => (c.sym, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2.asInstanceOf[FOLTerm])
  }
}

object Neg {
  def apply(sub: FOLFormula) = {
    val neg = sub.factory.createConnective(NegSymbol).asInstanceOf[FOLExpression]
    FOLApp(neg, sub).asInstanceOf[FOLFormula]
  }
<<<<<<< .working
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(NegC,sub) => Some( (sub.asInstanceOf[FOLFormula]) )
=======
}

object Neg {
  def apply(sub: FOLFormula) = App(NegC,sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub:FOLFormula) => Some( sub )
>>>>>>> .merge-right.r1940
    case _ => None
  }
}

object And {
  def apply(fs: List[FOLFormula]) : FOLFormula = fs match {
    case Nil => TopC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
<<<<<<< .working
  def apply(left: FOLFormula, right: FOLFormula) = {
    val and = left.factory.createConnective(AndSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(and, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(AndC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
=======
  def apply(left: FOLFormula, right: FOLFormula) = (App(App(AndC,left),right)).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left:FOLFormula),right:FOLFormula) => Some( (left,right) )
>>>>>>> .merge-right.r1940
    case _ => None
  }
}

object Or {
    def apply(fs: List[FOLFormula]) : FOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
<<<<<<< .working
  def apply(left: FOLFormula, right: FOLFormula) = {
    val or = left.factory.createConnective(OrSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(or, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(OrC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
=======
  def apply(left: FOLFormula, right: FOLFormula) = App(App(OrC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left:FOLFormula),right:FOLFormula) => Some( (left,right) )
>>>>>>> .merge-right.r1940
    case _ => None
  }
}

object Imp {
<<<<<<< .working
  def apply(left: FOLFormula, right: FOLFormula) = {
    val imp = left.factory.createConnective(ImpSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(imp, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
      case FOLApp(FOLApp(ImpC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
=======
  def apply(left: FOLFormula, right: FOLFormula) = App(App(ImpC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left:FOLFormula),right:FOLFormula) => Some( (left,right) )
>>>>>>> .merge-right.r1940
      case _ => None
  }
}

private class ExQ extends FOLLambdaConst(ExistsSymbol, ->(->(Ti, To), To) )
private object ExQ {
  def apply() = new ExQ
  def unapply(v: FOLLambdaConst) = v match {
    case vo: ExQ => Some()
    case _ => None
  }
}

private class AllQ extends FOLLambdaConst( ForallSymbol, ->(->(Ti, To), To) )
private object AllQ {
  def apply() = new AllQ
  def unapply(v: FOLLambdaConst) = v match {
    case vo: AllQ => Some()
    case _ => None
  }
}

private object Ex {
  def apply(sub: FOLExpression) = {
    val ex = sub.factory.createConnective(ExistsSymbol).asInstanceOf[FOLExpression]
    FOLApp(ex, sub).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(c: ExQ, sub) => Some( sub )
    case _ => None
  }
}

private object All {
  def apply(sub: FOLExpression) = {
    val all = sub.factory.createConnective(ForallSymbol).asInstanceOf[FOLExpression]
    FOLApp(all, sub).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(c: AllQ, sub) => Some( sub )
    case _ => None
  }
}

object ExVar {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: FOLExpression) = expression match {
    case Ex(FOLAbs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: FOLExpression) = expression match {
    case All(FOLAbs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

<<<<<<< .working
=======
object getFreeVariablesFOL {
  def apply( f: FOLFormula ) = f.freeVariables.asInstanceOf[Set[FOLVar]]
}

object getVariablesFOL {
  def apply( f: FOLFormula ) = (f.freeVariables ++ f.boundVariables).asInstanceOf[Set[FOLVar]]
}

object FOLSubstitution
{
  def apply(f: FOLFormula, map: Map[FOLVar, FOLTerm]) : FOLFormula = {
    val sub = Substitution(map.asInstanceOf[Map[Var, FOLExpression]])
      sub( f.asInstanceOf[FOLExpression]
         ).asInstanceOf[FOLFormula]
  }

  def apply(t: FOLTerm, map: Map[FOLVar, FOLTerm]) : FOLTerm = { 
    val sub = Substitution(map.asInstanceOf[Map[Var, FOLTerm]])
      sub( t )  
  }

  def apply(f: FOLFormula, x: FOLVar, t: FOLTerm) : FOLFormula =
    apply( f, Map((x, t)) )

  def apply(f: FOLTerm, x: FOLVar, t: FOLTerm) : FOLTerm =
    apply( f, Map((x, t)) )

}
>>>>>>> .merge-right.r1940
