/*
 * projections.scala
 *
 */

package at.logic.transformations.ceres.projections

import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}
import scala.collection.immutable.HashSet

object Projections {
  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKProof ) : Set[LKProof] = apply(proof, Set.empty[FormulaOccurrence])

  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    implicit val c_ancs = cut_ancs
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {
      case Axiom(s) => Set(Axiom(s))
      case ForallRightRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a.formula, m, v, ForallRightRule.apply )
      case ExistsLeftRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a.formula, m, v, ExistsLeftRule.apply )
      case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, AndRightRule.apply )
      case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, OrLeftRule.apply )
      case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, ImpLeftRule.apply )
      case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a.formula, m, t, ForallLeftRule.apply )
      case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a.formula, m, t, ExistsRightRule.apply )
      case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a.formula, m, NegLeftRule.apply )
      case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a.formula, m, NegRightRule.apply )
      case ContractionLeftRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1.formula, a2.formula, m, ContractionLeftRule.apply)
      case ContractionRightRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1.formula, a2.formula, m, ContractionRightRule.apply)
      case OrRight1Rule(p, _, a, m) => handleUnaryRule( proof, p, a.formula,
        m.formula match { case Or(_, w) => w }, m, OrRight1Rule.apply)
      case OrRight2Rule(p, _, a, m) => handleUnaryRule( proof, p,
        m.formula match { case Or(w, _) => w }, a.formula, m, OrRight2Rule.apply)
      case AndLeft1Rule(p, _, a, m) => handleUnaryRule( proof, p, a.formula,
        m.formula match { case And(_, w) => w }, m, AndLeft1Rule.apply)
      case AndLeft2Rule(p, _, a, m) => handleUnaryRule( proof, p,
        m.formula match { case And(w, _) => w }, a.formula, m, AndLeft2Rule.apply)
      case ImpRightRule(p, _, a1, a2, m) => handleUnaryRule(proof, p, a1.formula, a2.formula, m, ImpRightRule.apply)
      case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply )
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply )
      case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a.formula, m, DefinitionLeftRule.apply )
      case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a.formula, m, DefinitionRightRule.apply )
      case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationLeft1Rule.apply )
      case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationLeft2Rule.apply )
      case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationRight1Rule.apply )
      case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationRight2Rule.apply )
      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val s1 = apply( p1, new_cut_ancs + a1 )
        val s2 = apply( p2, new_cut_ancs + a2 )
        handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs + a1 + a2 )
      }
      case _ => throw new Exception("No such a rule in Projections.apply")
    }
  }

  def handleBinaryESAnc( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, s1: Set[LKProof], s2: Set[LKProof],
    constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) =
    s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
      s ++ s2.map( p2 => constructor( p1, p2, proof.aux.head.head.formula, proof.aux.tail.head.head.formula ) ) )

  def getESAncs( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) =
    Pair( proof.root.antecedent.filter( fo => !cut_ancs.contains( fo ) ),
          proof.root.succedent.filter( fo => !cut_ancs.contains( fo ) ) )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof, s1: Set[LKProof], s2: Set[LKProof], cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  def weakenESAncs( esancs: Pair[Seq[FormulaOccurrence], Seq[FormulaOccurrence]], s: Set[LKProof] ) = {
    val wl = s.map( p => esancs._1.foldLeft( p )( (p, fo) => WeakeningLeftRule( p, fo.formula ) ) )
    wl.map( p => esancs._2.foldLeft( p )( (p, fo) => WeakeningRightRule( p, fo.formula ) ) )
  }

  def handleContractionRule( proof: LKProof, p: LKProof, a1: HOLFormula, a2: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
    {
      val s = apply( p, copySetToAncestor( cut_ancs ) )
      if (cut_ancs.contains( m ) ) s
      else s.map( pm => constructor( pm, a1) )
    }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: HOLFormula, w: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula, HOLFormula) => LKProof)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a, w ) )
  }

  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, m.formula ) )
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a, m.formula ) )
  }

  def handleNegRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a ) )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence, t: HOLExpression,
    constructor: (LKProof, HOLFormula, HOLFormula, HOLExpression) => LKProof)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains(m)) s
    else s.map( pm => constructor( pm, a, m.formula, t) )
  }

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: HOLFormula, a2: HOLFormula,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      handleBinaryESAnc( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: HOLFormula, a2: HOLFormula,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, HOLFormula, HOLFormula, HOLFormula) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
        s ++ s2.map( p2 => constructor( p1, p2, proof.aux.head.head.formula, proof.aux.tail.head.head.formula, m.formula ) )
      )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence, v: HOLVar,
    constructor: (LKProof, HOLFormula, HOLFormula, HOLVar) => LKProof)( implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else throw new Exception("The proof is not skolemized!") // s.map( p => constructor( p, a, m.formula, v ) )
  }

  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )
}

object DeleteTautology {
  def apply(l : List[Sequent]): List[Sequent] = {
    l.filter( seq => {
      seq.antecedent.toList.map(fo => fo.formula).intersect( seq.succedent.toList.map(fo => fo.formula) ) == List[Sequent]()
    } ).map(seq1 => DeleteReduntantFOfromSequent(seq1))
  }
}

object DeleteReduntantFOfromSequent {
  def apply(s : Sequent): Sequent = {
    implicit val factory = defaultFormulaOccurrenceFactory
    val setant = s.antecedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    val setsucc = s.succedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    Sequent(setant.map(f => factory.createFormulaOccurrence(f, Nil)), setsucc.map(f => factory.createFormulaOccurrence(f, Nil)))
  }
}

object DeleteRedundantSequents {
  private def member(seq : Sequent, l : List[Sequent]): Boolean = {
    l match {
      case seq1::ls => {
        if (seq.antecedent.toList.map(fo => fo.formula).toSet == seq1.antecedent.toList.map(fo => fo.formula).toSet &&
            seq.succedent.toList.map(fo => fo.formula).toSet == seq1.succedent.toList.map(fo => fo.formula).toSet
        ) true
        else member(seq, ls)
      }
      case _ => false
    }
  }

  def apply(l : List[Sequent]): List[Sequent] = {
    l match {
      case x::ls => {
        val new_ls = apply(ls)
        if (member(x, new_ls))
          new_ls
        else
          x::new_ls
      }
      case _ => List[Sequent]()
    }
  }
}

