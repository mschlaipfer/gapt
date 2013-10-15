/*
 * fol.scala
 */

package at.logic.language.fol

import at.logic.language.lambda._
import at.logic.language.hol.{HOLExpression, HOLVar, HOLConst, HOLApp, HOLAbs, Formula}
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
    case FOLConst(x,t) => x.toString + ": " + t.toString
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
    /* TODO: this method usually fails if layers got mixed (a fol structure contains a hol structure). the cli
     *       throws this exception when it tries to print such a malformed structure, but this is hard to see.
     *       should we print a warning instead? */
    /* Current status: print a warning, since algorithms for typed lambda calculus may create partial lambda terms
       which are later completed. This only surfaces when one tries to print debug output. 
       TODO: LAYERS MUST NOT GET MIXED. */
    case _ =>
      val r = super.toString
      println("WARNING: Trying to do a string conversion on a term which is not a (full) FOL expression: "+r)
      r
    }

    override def freeVariables : List[FOLVar] = super.freeVariables.asInstanceOf[List[FOLVar]]

    override def factory : FactoryA = FOLFactory

}

trait FOLFormula extends FOLExpression with Formula {

  // Instantiates a term in a quantified formula (using the first quantifier).
  def instantiate(t: FOLTerm) = this match {
    case AllVar(v, form) =>
      val sub = Substitution(v, t)
      sub(form)
    case ExVar(v, form) => 
      val sub = Substitution(v, t)
      sub(form)
    case _ => throw new Exception("ERROR: trying to replace variables in a formula without quantifier.") 
  }

  // Instantiates all quantifiers of the formula with the terms in lst.
  // OBS: the number of quantifiers in the formula must greater or equal than the
  // number of terms in lst.
  def instantiateAll(lst: List[FOLTerm]) : FOLFormula = {
  lst match {
    case Nil => this
    case h :: t => this.instantiate(h).instantiateAll(t)
    }
  }

  // TODO: some of the methods below should work for FOL and HOL...

  // Transforms a formula to negation normal form (transforming also
  // implications into disjunctions)
  def toNNF : FOLFormula = this match {
    case Atom(_,_) => this
    case Function(_,_) => this
    case Imp(f1,f2) => Or((Neg(f1)).toNNF, f2.toNNF)
    case And(f1,f2) => And(f1.toNNF, f2.toNNF)
    case Or(f1,f2) => Or(f1.toNNF, f2.toNNF)
    case ExVar(x,f) => ExVar(x, f.toNNF)
    case AllVar(x,f) => AllVar(x, f.toNNF)
    case Neg(f) => f match {
      case Atom(_,_) => Neg(f)
      case Function(_,_) => Neg(f)
      case Neg(f1) => f1.toNNF
      case Imp(f1,f2) => And(f1.toNNF, Neg(f2.toNNF))
      case And(f1,f2) => Or(Neg(f1).toNNF, Neg(f2).toNNF)
      case Or(f1,f2) => And(Neg(f1).toNNF, Neg(f2).toNNF)
      case ExVar(x,f) => AllVar(x, Neg(f).toNNF)
      case AllVar(x,f) => ExVar(x, Neg(f).toNNF)
      case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
    }
    case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
  }

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
    case _ => throw new Exception("ERROR: Unexpected case while distributing Ors over Ands.")
  }

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

  // Returns the quantifier free part of a prenex formula
  def getMatrix : FOLFormula = {
    assert(this.isPrenex)
    this match {
      case Var(_,_) |
           Atom(_,_) |
           Imp(_,_) |
           And(_,_) |
           Or(_,_) |
           Neg(_) => this
      case ExVar(x,f0) => f0.getMatrix
      case AllVar(x,f0) => f0.getMatrix
      case _ => throw new Exception("ERROR: Unexpected case while extracting the matrix of a formula.")
    }
  }
}

trait FOLTerm extends FOLExpression { require( exptype == Ti() ) }

class FOLApp protected[fol] (function: FOLExpression, arg: FOLExpression) extends HOLApp(function, arg) with FOLExpression
object FOLApp {
  def apply(f: FOLExpression, arg: FOLExpression) = f.exptype match {
    case ->(_, To()) => new FOLApp(f, arg) with FOLFormula
    case ->(_, Ti()) => new FOLApp(f, arg) with FOLTerm
    case _ => new FOLApp(f, arg)
  }
  def unapply(e: FOLExpression) = e match {
    case a: FOLApp => Some( (a.function.asInstanceOf[FOLExpression], a.arg.asInstanceOf[FOLExpression]) )
    case _ => None
  }
}

class FOLAbs protected[fol] (variable: FOLVar, term: FOLExpression) extends HOLAbs(variable, term) with FOLExpression
object FOLAbs {
  def apply(variable: FOLVar, expression: FOLExpression) = new FOLAbs(variable, expression)
  def unapply(e: FOLExpression) = e match {
    case a: FOLAbs => Some( (a.variable.asInstanceOf[FOLVar], a.term.asInstanceOf[FOLExpression]) )
    case _ => None
  }
}

class FOLVar (sym: SymbolA) extends HOLVar(sym, Ti()) with FOLTerm
object FOLVar {
  def apply(name: String) = new FOLVar(StringSymbol(name))
  def unapply(exp: FOLExpression) = exp match {
    case v: FOLVar => Some( v.name )
    case _ => None
  }
}

class FOLConst (sym: SymbolA, exptype: TA) extends HOLConst(sym, exptype) with FOLExpression
object FOLConst {
  def apply(name: String) = new FOLConst(StringSymbol(name), Ti()) with FOLTerm
  def apply(name: String, exptype: TA) = exptype match {
    case To() => new FOLConst(StringSymbol(name), exptype) with FOLFormula
    case Ti() => new FOLConst(StringSymbol(name), exptype) with FOLTerm
    case _ => new FOLConst(StringSymbol(name), exptype)
  }
  def unapply(exp: FOLExpression) = exp match {
    case c: FOLConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

case object TopC extends FOLConst(TopSymbol, To()) with FOLFormula
case object BottomC extends FOLConst(BottomSymbol, To()) with FOLFormula
case object NegC extends FOLConst(NegSymbol, To() -> To() )
case object AndC extends FOLConst(AndSymbol, To() -> (To() -> To()))
case object OrC extends FOLConst(OrSymbol,   To() -> (To() -> To()))
case object ImpC extends FOLConst(ImpSymbol, To() -> (To() -> To()))
case object EqC extends FOLConst(EqSymbol,   Ti() -> (Ti() -> To()))

object Equation {
    def apply(left: FOLTerm, right: FOLTerm) = {
      FOLApp(FOLApp(EqC, left),right).asInstanceOf[FOLFormula]
    }
    def unapply(expression: FOLExpression) = expression match {
        case FOLApp(FOLApp(EqC,left),right) => Some( left.asInstanceOf[FOLTerm],right.asInstanceOf[FOLTerm] )
        case _ => None
    }
  }

// FOL atom of the form P(t_1,...,t_n)
object Atom {
  def apply(head: FOLVar, args: List[FOLExpression]): FOLFormula = apply_(head, args).asInstanceOf[FOLFormula]
  def apply(head: FOLConst, args: List[FOLExpression]): FOLFormula = apply_(head, args).asInstanceOf[FOLFormula]
  private def apply_(head: FOLExpression, args: List[FOLExpression]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLConst,_) if c.isLogicalSymbol => None
    case FOLApp(FOLApp(c: FOLConst,_),_) if c.isLogicalSymbol => None
    case FOLApp(_,_) if (expression.exptype == To()) => Some( unapply_(expression) )
    case FOLConst(_) if (expression.exptype == To()) => Some( (expression, Nil) )
    case FOLVar(_) if (expression.exptype == To()) => Some( (expression, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (FOLExpression, List[FOLExpression]) = e match {
    case v: FOLVar => (v, Nil)
    case c: FOLConst => (c, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

// FOL function of the form f(t_1,...,t_n)
object Function {
  def apply(head: FOLVar, args: List[FOLExpression]): FOLTerm = apply_(head, args).asInstanceOf[FOLTerm]
  def apply(head: FOLConst, args: List[FOLExpression]): FOLTerm = apply_(head, args).asInstanceOf[FOLTerm]
  private def apply_(head: FOLExpression, args: List[FOLExpression]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLConst,_) if c.isLogicalSymbol => None
    case FOLApp(FOLApp(c: FOLConst,_),_) if c.isLogicalSymbol => None
    case FOLApp(_,_) if (expression.exptype != To()) => 
      val t = unapply_(expression) 
      Some( (t._1, t._2) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (FOLExpression, List[FOLExpression]) = e match {
    case v: FOLVar => (v, Nil)
    case c: FOLConst => (c, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}

object Neg {
  def apply(sub: FOLFormula) = FOLApp(NegC,sub).asInstanceOf[FOLFormula]
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(NegC,sub) => Some( (sub.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: Seq[FOLFormula]) : FOLFormula = fs match {
    case Nil => TopC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
  def apply(left: FOLFormula, right: FOLFormula) = (FOLApp(FOLApp(AndC,left),right)).asInstanceOf[FOLFormula]
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(AndC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Or {
    def apply(fs: Seq[FOLFormula]) : FOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
  def apply(left: FOLFormula, right: FOLFormula) = FOLApp(FOLApp(OrC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(OrC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: FOLFormula, right: FOLFormula) = FOLApp(FOLApp(ImpC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: FOLExpression) = expression match {
      case FOLApp(FOLApp(ImpC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
      case _ => None
  }
}

class ExQ protected[fol] extends FOLConst(ExistsSymbol, ->(->(Ti(), To()), To()) )
object ExQ {
  def unapply(v: FOLConst) = v match {
    case vo: ExQ => Some()
    case _ => None
  }
}

class AllQ protected[fol] extends FOLConst( ForallSymbol, ->(->(Ti(), To()), To()) )
object AllQ {
  def unapply(v: FOLConst) = v match {
    case vo: AllQ => Some()
    case _ => None
  }
}

object Ex {
  def apply(sub: FOLExpression) = FOLApp(new ExQ, sub).asInstanceOf[FOLFormula]
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(c: ExQ, sub) => Some( sub )
    case _ => None
  }
}

object All {
  def apply(sub: FOLExpression) = FOLApp(new AllQ, sub).asInstanceOf[FOLFormula]
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

/*
object BinaryLogicSymbol {
  def unapply(expression: FOLExpression) = expression match {
    case And(l, r) => Some( (AndC, l, r) )
    case Or(l, r) => Some( (OrC, l, r) )
    case Imp(l, r) => Some( (ImpC, l, r) )
    case _ => None
  }
}
*/

/*********************** Factories *****************************/

object FOLFactory extends FactoryA {
  def createVar( name: String, exptype: TA ) : FOLVar = exptype match {
    case Ti() => new FOLVar(StringSymbol(name))
    case To() => throw new Exception("In FOL, of type 'o' only constants may be created.")
    case ->(tr, ta) => throw new Exception("In FOL, of type 'a -> b' only constants may be created.")
  }

  def createCons( name: String, exptype: TA ) : FOLConst = exptype match {
    case Ti() => new FOLConst(StringSymbol(name), Ti())
    case To() => new FOLConst(StringSymbol(name), To()) with FOLFormula
    case FunctionType(Ti(), _) => new FOLConst(StringSymbol(name), exptype) with FOLExpression
    case FunctionType(To(),_) =>  new FOLConst(StringSymbol(name), exptype) with FOLFormula
  }


  def createVar( name: String ) : FOLVar = createVar( name, Ti() )

  //remark: in contrast to earlier times, you can only create fol applications from fol expressions
  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : FOLApp = {
    require( fun.isInstanceOf[FOLExpression] ,
      "You are trying to use the FOL factory to create an application of a non-fol first argument "+fun+"!")
    require( arg.isInstanceOf[FOLExpression] ,
      "You are trying to use the FOL factory to create an application of a non-fol second argument "+arg+"!")
    val fun_ = fun.asInstanceOf[FOLExpression]
    val arg_ = arg.asInstanceOf[FOLExpression]
    fun.exptype match {
      case ->(_, To()) => new FOLApp(fun_, arg_) with FOLFormula
      case ->(_, Ti()) => new FOLApp(fun_, arg_) with FOLTerm
      case _ =>  new FOLApp(fun_, arg_)
    }
  }

   def createAbs( variable: Var, exp: LambdaExpression ) : FOLAbs =
     new FOLAbs( variable.asInstanceOf[FOLVar], exp.asInstanceOf[FOLExpression] )
}


