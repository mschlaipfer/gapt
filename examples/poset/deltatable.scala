package at.logic.gapt.examples.poset

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.grammars.DeltaTableMethod
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.Sat4j

object dtable extends Script {

  val constructedProof = eliminateCutsET( LKToExpansionProof( proof.cycleImpliesEqual4 ) )
  //  println( extractRecSchem( proof.cycleImpliesEqual4 ) )
  //  InstanceTermEncoding( proof.cycleImpliesEqual4 )._1.toSeq sortBy { _.toString } foreach println

  if ( false ) {
    val removeEq = Map( EqC( Ti ) -> FOLAtomConst( "E", 2 ) )
    val Some( automaticProof ) =
      Prover9.getExpansionProof(
        TermReplacement( proof.cycleImpliesEqual4.endSequent, removeEq.toMap )
      ) map { TermReplacement( _, removeEq.map( _.swap ) ) }
    val Some( autoMin ) = minimalExpansionSequent( automaticProof, Sat4j )
  }

  CutIntroduction.compressToLK( constructedProof, hasEquality = false,
    method = DeltaTableMethod( singleQuantifier = false, subsumedRowMerging = true, keyLimit = Some( 3 ) ),
    verbose = true )

}
