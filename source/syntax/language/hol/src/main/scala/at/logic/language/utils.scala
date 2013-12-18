/*
 * Simple functions that operate on HOL-expressions
 *
 */

package at.logic.language.hol

import at.logic.language.lambda.{freeVariables => freeVariablesLambda, rename => renameLambda}
import at.logic.language.hol.logicSymbols.LogicalSymbolA

object freeVariables {
  def apply(e: HOLExpression) : List[HOLVar] = freeVariablesLambda(e).asInstanceOf[List[HOLVar]]
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  def apply(v: HOLVar, blacklist: List[HOLVar]) : HOLVar = renameLambda(v, blacklist).asInstanceOf[HOLVar]
}

// Instantiates a term in a quantified formula (using the first quantifier).
object instantiate {
  def apply(f: HOLFormula, t: HOLExpression) : HOLFormula = f match {
    case AllVar(v, form) =>
      val sub = Substitution(v, t)
      sub(form)
    case ExVar(v, form) => 
      val sub = Substitution(v, t)
      sub(form)
    case _ => throw new Exception("ERROR: trying to replace variables in a formula without quantifier.") 
  }
}

object containsQuantifier {
  def apply(e: HOLExpression) : Boolean = e match {
    case HOLVar(x,tpe) => false
    case HOLConst(x,tpe) => false
    case Atom(x, args) => false
    case And(x,y) => containsQuantifier(x) || containsQuantifier(y)
    case Or(x,y) => containsQuantifier(x) || containsQuantifier(y)
    case Imp(x,y) => containsQuantifier(x) || containsQuantifier(y)
    case HArray(x,y) => containsQuantifier(x) || containsQuantifier(y)
    case Neg(x) => containsQuantifier(x)
    case ExVar(x,f) => true
    case AllVar(x,f) => true
    // Is this really necessary?
    case HOLAbs(v, exp) => containsQuantifier(exp)
    case HOLApp(l, r) => containsQuantifier(l) || containsQuantifier(r)
    case _ => throw new Exception("Unrecognized symbol.")
  }
}

object isPrenex {
  def apply(e: HOLExpression) : Boolean = e match {
    case HOLVar(_,_) => true
    case HOLConst(_,_) => true
    case Atom(_,_) => true
    case Neg(f) => !containsQuantifier(f)
    case And(f1,f2) => !containsQuantifier(f1) && !containsQuantifier(f2)
    case Or(f1,f2) => !containsQuantifier(f1) && !containsQuantifier(f2)
    case Imp(f1,f2) => !containsQuantifier(f1) && !containsQuantifier(f2)
    case ExVar(v,f) => isPrenex(f)
    case AllVar(v,f) => isPrenex(f)
    case _ => throw new Exception("ERROR: Unknow operator encountered while checking for prenex formula: " + this)
  }
}

object isAtom {
  def apply(e: HOLExpression) : Boolean = e match {
    case Atom(_,_) => true
    case _ => false
  }
}

object subTerms {
  def apply(e: HOLExpression) : List[HOLExpression] = e match {
    case HOLVar(_,_) => List(e)
    case HOLConst(_,_) => List(e)
    case Atom(_, args) =>  e +: args.flatMap( a => subTerms(a) )
    case Function(_,args,_)  =>  e +: args.flatMap( a => subTerms(a) )
    case And(x,y) => e +: (subTerms(x) ++ subTerms(y))
    case Or(x,y) => e +: (subTerms(x) ++ subTerms(y))
    case Imp(x,y) => e +: (subTerms(x) ++ subTerms(y))
    case Neg(x) => e +: subTerms(x)
    case AllVar(_, x) => e +: subTerms(x)
    case ExVar(_, x) => e +: subTerms(x)
    case HOLAbs(_, x) => e +: subTerms(x)
    case HOLApp(x, y) => e +: (subTerms(x) ++ subTerms(y))
    case _ => throw new Exception("Unrecognized symbol.")
  }
}

object isLogicalSymbol {
  def apply(e: HOLExpression) : Boolean = e match {
    case x : HOLConst => x.sym.isInstanceOf[LogicalSymbolA]
    case _ => false
  }
}
