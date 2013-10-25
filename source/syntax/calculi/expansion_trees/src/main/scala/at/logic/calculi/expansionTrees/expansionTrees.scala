
package at.logic.calculi.expansionTrees

import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.utils.ds.trees._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._

trait ExpansionTree extends TreeA[Option[HOLFormula],Option[HOLExpression]]

case class WeakQuantifier(formula: HOLFormula, instances: Seq[Tuple2[ExpansionTree, HOLExpression]])
  extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = instances.map(x => (x._1,Some(x._2)))
}

case class StrongQuantifier(formula: HOLFormula, variable: HOLVar, selection: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = List(Pair(selection,Some(variable)))
}

case class And(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Or(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Imp(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Not(tree: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(tree,None))
}
case class Atom(formula: HOLFormula) extends ExpansionTree with TerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
}

object toFormula {
  def apply(tree: ExpansionTree): HOLFormula = tree match {
    case Atom(f) => f
    case Not(t1) => Neg(toFormula(t1))
    case And(t1,t2) => AndHOL(toFormula(t1), toFormula(t2))
    case Or(t1,t2) => OrHOL(toFormula(t1), toFormula(t2))
    case Imp(t1,t2) => ImpHOL(toFormula(t1), toFormula(t2))
    case WeakQuantifier(f,_) => f
    case StrongQuantifier(f,_,_) => f
  }
}

// Returns the end-sequent of the proof represented by this expansion tree
object toSequent {
  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : Sequent = {
    // TODO: there MUST be an easier way...
    val ant = ep._1.map( et => defaultFormulaOccurrenceFactory.createFormulaOccurrence(toFormula(et), Nil) )
    val cons = ep._2.map( et => defaultFormulaOccurrenceFactory.createFormulaOccurrence(toFormula(et), Nil) )

    Sequent(ant, cons)
  }
}

// Builds an expansion tree given a quantifier free formula
object qFreeToExpansionTree {
  def apply(f : HOLFormula) : ExpansionTree= f match {
    case AtomHOL(_,_) => Atom(f)
    case Neg(f) => Not(qFreeToExpansionTree(f))
    case AndHOL(f1,f2) => And(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case OrHOL(f1,f2) => Or(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case ImpHOL(f1,f2) => Imp(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case _ => throw new Exception("Error transforming a quantifier-free formula into an expansion tree: " + f)
  }
}

