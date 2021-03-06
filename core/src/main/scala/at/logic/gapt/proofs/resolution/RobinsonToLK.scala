
package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol.structuralCNF
import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._

import scala.collection.mutable
import scalaz.\/-

object RobinsonToLK {
  /**
   * Converts a resolution refutation of a sequent into an LK proof.
   *
   * @param resolutionProof  Resolution refutation ending in the empty clause,
   *                         the input clauses are required to be from the CNF of endSequent.
   * @param endSequent  End sequent that resolutionProof refutes.
   * @return LKProof ending in endSequent.
   */
  def apply( resolutionProof: ResolutionProof, endSequent: HOLSequent ): LKProof = {
    assert( resolutionProof.conclusion.isEmpty )
    apply( resolutionProof, endSequent, PCNF( endSequent, _ ) )
  }

  def apply( resolutionProof: ResolutionProof, endSequent: HOLSequent,
             justifications: Map[HOLClause, structuralCNF.Justification],
             definitions:    Map[HOLAtomConst, LambdaExpression],
             addWeakenings:  Boolean ): LKProof = {
    require( resolutionProof.conclusion.isEmpty )

    import structuralCNF.{ ProjectionFromEndSequent, Definition }

    val projections = justifications map {
      case ( clause, ProjectionFromEndSequent( proj, index ) ) =>
        val \/-( projWithDef ) = PropositionalExpansionProofToLK( ExpansionProof( proj ++ clause.map( ETAtom( _, false ), ETAtom( _, true ) ) ) )
        clause -> projWithDef

      case ( clause, Definition( newAtom, expansion ) ) =>
        val i = clause indexOf newAtom
        val \/-( p ) = PropositionalExpansionProofToLK( ExpansionProof( clause.map( ETAtom( _, false ), ETAtom( _, true ) ).updated( i, expansion ) ) )
        clause -> DefinitionRule( p, expansion.shallow, newAtom, i isSuc )
    }

    val proofWithDefs = apply( resolutionProof, endSequent, projections, addWeakenings )
    DefinitionElimination( definitions.toMap )( proofWithDefs )
  }

  /**
   * Converts a resolution derivation into an LK proof with axioms.
   *
   * @param resolutionDerivation  Resolution derivation.
   * @return  LK proof ending in the conclusion of resolutionDerivation,
   *          where all TheoryAxioms occur as InputClauses in resolutionDerivation.
   */
  def apply( resolutionDerivation: ResolutionProof ): LKProof =
    apply( resolutionDerivation, resolutionDerivation.conclusion, TheoryAxiom )

  /**
   * Converts a resolution derivation into an LK proof.
   *
   * Input clauses in the resolution derivation are replaced with the LK proofs returned by createAxiom.
   * Their end-sequents are required to be the input clause plus possibly some formulas from endSequent.
   *
   * @param resolutionDerivation  Resolution derivation.
   * @param endSequent  Additional formulas in the end-sequent of the returned LK proof.
   * @param createAxiom  Gives the replacement LK proofs for the input clauses.
   * @return  LK proof ending in endSequent ++ resolutionDerivation.conclusion.
   */
  def apply( resolutionDerivation: ResolutionProof, endSequent: HOLSequent, createAxiom: HOLClause => LKProof, addWeakenings: Boolean = true ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, p match {
      case TautologyClause( atom )   => LogicalAxiom( atom )
      case ReflexivityClause( term ) => ReflexivityAxiom( term )
      case InputClause( cls ) =>
        ContractionMacroRule( WeakeningMacroRule( createAxiom( cls ), cls, strict = false ), endSequent ++ cls, strict = false )
      case Factor( p1, idx1 @ Ant( _ ), idx2 ) =>
        ContractionLeftRule( f( p1 ), p1.conclusion( idx1 ) )
      case Factor( p1, idx1 @ Suc( _ ), idx2 ) =>
        ContractionRightRule( f( p1 ), p1.conclusion( idx1 ) )
      case Instance( p1, s ) if s.isIdentity => f( p1 )
      case Instance( p1, s )                 => s( f( p1 ) )
      case Resolution( p1, idx1, p2, idx2 ) =>
        ContractionMacroRule(
          CutRule( f( p1 ), f( p2 ), p1.conclusion( idx1 ) ),
          endSequent ++ p.conclusion, strict = false
        )
      case p @ Paramodulation( p1, eq, p2, lit @ Ant( _ ), poss, dir ) =>
        ContractionMacroRule(
          ParamodulationLeftRule( f( p1 ), p1.conclusion( eq ),
            f( p2 ), p2.conclusion( lit ), p.rewrittenAtom ),
          endSequent ++ p.conclusion, strict = false
        )
      case p @ Paramodulation( p1, eq, p2, lit @ Suc( _ ), poss, dir ) =>
        val ( p1New, p2New ) = ( f( p1 ), f( p2 ) )
        ContractionMacroRule(
          ParamodulationRightRule( p1New, p1.conclusion( eq ),
            p2New, p2.conclusion( lit ), p.rewrittenAtom ),
          endSequent ++ p.conclusion, strict = false
        )
    } )
    val rproof = f( eliminateSplitting( resolutionDerivation ) )
    if ( addWeakenings ) WeakeningContractionMacroRule( rproof, endSequent )
    else ContractionMacroRule( rproof )
  }

}
