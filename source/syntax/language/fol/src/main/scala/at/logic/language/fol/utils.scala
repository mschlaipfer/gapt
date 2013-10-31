/**
 * Helper functions for first order logic
 */

package at.logic.language.fol

import at.logic.language.lambda.types._
import at.logic.language.lambda.{freeVariables => freeVariablesLambda, rename => renameLambda}
import at.logic.language.hol.isPrenex

object freeVariables {
  def apply(e: FOLExpression) : List[FOLVar] = freeVariablesLambda(e).asInstanceOf[List[FOLVar]]
}

// Instantiates a term in a quantified formula (using the first quantifier).
object instantiate {
  def apply(f: FOLFormula, t: FOLTerm) : FOLFormula = f match {
    case AllVar(v, form) =>
      val sub = Substitution(v, t)
      sub(form)
    case ExVar(v, form) => 
      val sub = Substitution(v, t)
      sub(form)
    case _ => throw new Exception("ERROR: trying to replace variables in a formula without quantifier.") 
  }
}

// get a new variable/constant (similar to the current and) different from all 
// variables/constants in the blackList, returns this variable if this variable 
// is not in the blackList
object rename {
  def apply(v: FOLVar, blackList: List[FOLVar]) : FOLVar = renameLambda(v, blackList).asInstanceOf[FOLVar]
  def apply(c: FOLConst, blackList: List[FOLConst]) : FOLConst = renameLambda(c, blackList).asInstanceOf[FOLConst]
}

// Instantiates all quantifiers of the formula with the terms in lst.
// OBS: the number of quantifiers in the formula must greater or equal than the
// number of terms in lst.
object instantiateAll {
  def apply(f: FOLFormula, lst: List[FOLTerm]) : FOLFormula = lst match {
    case Nil => f
    case h :: t => instantiateAll(instantiate(f, h), t)
  }
}

// TODO: some of the methods below should work for FOL and HOL...

// Transforms a formula to negation normal form (transforming also
// implications into disjunctions)
object toNNF {
  def apply(f: FOLFormula) : FOLFormula = f match {
    case Atom(_,_) => f
    case Function(_,_) => f
    case Imp(f1,f2) => Or(toNNF(Neg(f1)), toNNF(f2))
    case And(f1,f2) => And(toNNF(f1), toNNF(f2))
    case Or(f1,f2) => Or(toNNF(f1), toNNF(f2))
    case ExVar(x,f) => ExVar(x, toNNF(f))
    case AllVar(x,f) => AllVar(x, toNNF(f))
    case Neg(f) => f match {
      case Atom(_,_) => Neg(f)
      case Function(_,_) => Neg(f)
      case Neg(f1) => toNNF(f1)
      case Imp(f1,f2) => And(toNNF(f1), toNNF(Neg(f2)))
      case And(f1,f2) => Or(toNNF(Neg(f1)), toNNF(Neg(f2)))
      case Or(f1,f2) => And(toNNF(Neg(f1)), toNNF(Neg(f2)))
      case ExVar(x,f) => AllVar(x, toNNF(Neg(f)))
      case AllVar(x,f) => ExVar(x, toNNF(Neg(f)))
      case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
    }
    case _ => throw new Exception("ERROR: Unexpected case while transforming to negation normal form.")
  }
}

// Distribute Ors over Ands
object distribute {
  def apply(f: FOLFormula) : FOLFormula = f match {
    case Atom(_,_) => f
    // Negation has only atomic scope
    case Neg(Atom(_,_)) => f
    case And(f1, f2) => And(distribute(f1), distribute(f2))
    case Or(f1, And(f2,f3)) => And(distribute(Or(f1,f2)), distribute(Or(f1,f3)))
    case Or(And(f1,f2), f3) => And(distribute(Or(f1,f3)), distribute(Or(f2,f3)))
    case Or(f1, f2) => Or(distribute(f1), distribute(f2))
    case _ => throw new Exception("ERROR: Unexpected case while distributing Ors over Ands.")
  }
}

// Transforms a formula to conjunctive normal form
// 1. Transform to negation normal form
// 2. Distribute Ors over Ands
// OBS: works for propositional formulas only
// TODO: tests for this
object toCNF {
  def apply(f: FOLFormula) : FOLFormula = distribute(toNNF(f))
}

object numOfAtoms {
  def apply(f: FOLFormula) : Int = f match {
    case Atom(_,_) => 1
    case Function(_,_) => 1
    case Imp(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case And(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case Or(f1,f2) => numOfAtoms(f1) + numOfAtoms(f2)
    case ExVar(x,f) => numOfAtoms(f)
    case AllVar(x,f) => numOfAtoms(f)
    case Neg(f) => numOfAtoms(f)
    case _ => throw new Exception("ERROR: Unexpected case while counting the number of atoms.")
  }
}

// Returns the quantifier free part of a prenex formula
object getMatrix {
  def apply(f: FOLFormula) : FOLFormula = {
    assert(isPrenex(f))
    f match {
      case FOLVar(_) |
           FOLConst(_,_) |
           Atom(_,_) |
           Imp(_,_) |
           And(_,_) |
           Or(_,_) |
           Neg(_) => f
      case ExVar(x,f0) => getMatrix(f0)
      case AllVar(x,f0) => getMatrix(f0)
      case _ => throw new Exception("ERROR: Unexpected case while extracting the matrix of a formula.")
    }
  }
}

// Transforms a list of literals into an implication formula, with negative 
// literals on the antecedent and positive literals on the succedent.
object reverseCNF {
  def apply(f: List[FOLFormula]) : FOLFormula = {
    val (ant, succ) = f.foldRight((List[FOLFormula](), List[FOLFormula]())) {
      case (f, (ant, succ)) => f match {
        case Neg(a) => (a::ant, succ)
        case a => (ant, a::succ)
      }
    }
    val conj = And(ant)
    val disj = Or(succ)
    Imp(conj, disj)
  }
}

object Utils {

  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: String, k: Int ) : FOLTerm =
    if ( k == 0 ) a else Function( f, iterateTerm( a, f, k-1 )::Nil )

  // Constructs the FOLTerm s^k(0)
  def numeral( k: Int ) = iterateTerm( FOLConst( "0" ).asInstanceOf[FOLTerm], "s" , k )


  // TODO: maybe these functions should go to listSupport in dssupport in the
  // utils project.

  def removeDoubles[T](l : List[T]) : List[T] = {
    removeDoubles_(l.reverse).reverse
  }

  private def removeDoubles_[T](l : List[T]) : List[T] = {
    l match {
      case head :: tail =>
        if (tail.contains(head))
          removeDoubles(tail)
        else
          head :: removeDoubles(tail)
      case Nil => Nil
    }
  }

  //auxiliary function which removes duplications from list of type:
  //List[List[(String, Tree[AnyRef], Set[FormulaOccurrence])]]
  //and type
  ////List[List[(String, Tree[AnyRef], (Set[FormulaOccurrence], Set[FormulaOccurrence]))]]

  def removeDoubles3[T,R](l : List[Tuple3[String,T,R]]) : List[Tuple3[String,T,R]] = {
    l match {
      case head :: tail =>
        if (tail.map(tri => tri._3).contains(head._3))
          removeDoubles3(tail)
        else
          head :: removeDoubles3(tail)
      case Nil => Nil
    }
  }
}
