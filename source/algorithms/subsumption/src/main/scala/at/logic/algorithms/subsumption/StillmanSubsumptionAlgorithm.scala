/*
 * StillmanSubsumptionAlgorithm.scala
 *
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching._
import at.logic.language.hol.{HOLExpression, Substitution => SubstitutionHOL, Neg => NegHOL, HOLVar, freeVariables => freeVariablesHOL}
import at.logic.language.fol.{FOLFormula, FOLExpression, Substitution => SubstitutionFOL, Neg => NegFOL, FOLVar, freeVariables => freeVariablesFOL}
import at.logic.calculi.lk.base.FSequent

object StillmanSubsumptionAlgorithmHOL extends SubsumptionAlgorithm {
  val matchAlg = NaiveIncompleteMatchingAlgorithm
<<<<<<< .working
  def subsumes(s1: FSequent, s2: FSequent): Boolean =
    // TODO: what is the second map doing????
    ST(s1._1.map(x => NegHOL(x)) ++ s1._2.map(x => x),
      s2._1.map(x => NegHOL(x)) ++ s2._2.map(x => x), 
      SubstitutionHOL(), 
      (s2._1.flatMap(x => freeVariablesHOL(x)) ++ s2._2.flatMap(x => freeVariablesHOL(x))).toList)
=======
  def subsumes(s1: FSequent, s2: FSequent): Boolean = subsumes_by(s1,s2).nonEmpty
>>>>>>> .merge-right.r1940

<<<<<<< .working
  def ST(ls1: Seq[HOLExpression], ls2: Seq[HOLExpression], sub: SubstitutionHOL, restrictedDomain: List[HOLVar]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
=======
  def subsumes_by(s1: FSequent, s2: FSequent) : Option[Substitution[T]] = {
    val left = s1._1.map(x => neg(x)) ++ s1._2.map(x => x)
    val right = s2._1.map(x => neg(x)) ++ s2._2.map(x => x)
    val lv = remove_doubles(left.foldLeft(List[Var]())((l,f) => vars(f,l)))
    val rv = remove_doubles(right.foldLeft(List[Var]())((l,f) => vars(f,l)))
    val renames = rv.filter(x=> lv.contains(x))
    var count = 0
    val vg = new VariableNameGenerator(() => {count = count+1; "vg_{"+count+"}"})
    val (newnames, _) = renames.foldLeft((List[Var](), lv++rv))((pair,x) => {
      val v = vg(x, pair._2)
      (v::pair._1, v::pair._2)
    }  )

    val sub = Substitution[LambdaExpression](renames zip newnames)
    val rsub = Substitution[LambdaExpression](newnames zip renames)


    ST(left, right.map(sub), Substitution[T](), newnames) match {
      case None => None
      case Some(subst) => Some(Substitution[T](subst.map.map(x => (x._1, rsub(x._2).asInstanceOf[T]))))
    }
>>>>>>> .merge-right.r1940
  }
}

<<<<<<< .working
object StillmanSubsumptionAlgorithmFOL extends SubsumptionAlgorithm {
  val matchAlg = FOLMatchingAlgorithm
  def subsumes(s1: FSequent, s2: FSequent): Boolean =
    ST(s1._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s1._2.map(x => x.asInstanceOf[FOLFormula]),
      s2._1.map(x => NegFOL(x.asInstanceOf[FOLFormula])) ++ s2._2.map(x => x.asInstanceOf[FOLFormula]), 
      SubstitutionFOL(), 
      (s2._1.flatMap(x => freeVariablesFOL(x.asInstanceOf[FOLFormula])) ++ s2._2.flatMap(x => freeVariablesFOL(x.asInstanceOf[FOLFormula]))).toList)

  def ST(ls1: Seq[FOLExpression], ls2: Seq[FOLExpression], sub: SubstitutionFOL, restrictedDomain: List[FOLVar]): Boolean = ls1 match {
    case Nil => true // first list is exhausted
    case x::ls => val sx = sub(x); ls2.exists(t => matchAlg.matchTerm(sx, sub(t), restrictedDomain) match {
      case Some(sub2) => ST(ls, ls2, sub2 compose sub, restrictedDomain)
      case _ => false
    })
  }
=======
  def ST(ls1: Seq[LambdaExpression], ls2: Seq[LambdaExpression], sub: Substitution[T], restrictedDomain: List[Var])
   : Option[Substitution[T]] =
    ls1 match {
      case Nil => Some(sub) // first list is exhausted
      case x::ls =>
        val sx = sub(x.asInstanceOf[T]);
        //TODO: the original algorithm uses backtracking, this does not. check if this implementation is incomplete
        val nsubs = ls2.flatMap(t =>
          matchAlg.matchTerm(sx.asInstanceOf[T], sub(t.asInstanceOf[T]), restrictedDomain) match {
            case Some(sub2) =>
              val nsub : Substitution[T] = sub2.compose(sub)
              val st = ST(ls, ls2, nsub, restrictedDomain ++ nsub.map.flatMap(_._2.freeVariables))
              if (st.nonEmpty) st::Nil else Nil
            case _ => Nil
      })
      if (nsubs.nonEmpty) nsubs.head else None

  }

  // should be generic but right now supports only hol and fol
  private def neg(f: Formula) = if (f.isInstanceOf[FOLFormula]) FOLNeg(f.asInstanceOf[FOLFormula]) else Neg(f.asInstanceOf[HOLFormula])
>>>>>>> .merge-right.r1940

  private def vars(e:LambdaExpression, vs : List[Var]) : List[Var] = e match {
    case Var(_:VariableSymbolA, _) => e.asInstanceOf[Var] :: vs
    case Var(_,_) => vs
    case App(s,t) => vars(s, vars(t, vs))
    case Abs(x,t) => vars(t,x::vs)
  }

  private def remove_doubles[T](l:List[T]) : List[T] = remove_doubles_(l.reverse).reverse
  private def remove_doubles_[T](l:List[T]) : List[T] = l match {
    case Nil => Nil
    case x::xs => if (xs contains x) remove_doubles_(xs) else x::remove_doubles_(xs)
  }
}
