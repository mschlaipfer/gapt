package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLClause, HOLSequent }

object renameConstantsToFi {
  private def mkName( i: Int ) = s"f$i"
  private def getRenaming( seq: HOLSequent ): Map[Const, Const] = getRenaming( constants( seq ) )
  private def getRenaming( cnf: Traversable[HOLClause] ): Map[Const, Const] =
    getRenaming( cnf.flatMap( constants( _ ) ).toSet )
  private def getRenaming( constants: Set[Const] ): Map[Const, Const] =
    constants.toSeq.zipWithIndex.map {
      case ( c @ EqC( _ ), _ ) => c -> c
      case ( c, i )            => c -> Const( mkName( i ), c.exptype )
    }.toMap
  private def invertRenaming( map: Map[Const, Const] ) = map.map( _.swap )

  def apply( seq: HOLSequent ): ( HOLSequent, Map[Const, Const], Map[Const, Const] ) = {
    val renaming = getRenaming( seq )
    val renamedSeq = TermReplacement( seq, renaming.toMap )
    ( renamedSeq, renaming, invertRenaming( renaming ) )
  }
  def apply( cnf: Traversable[HOLClause] ): ( Traversable[HOLClause], Map[Const, Const], Map[Const, Const] ) = {
    val renaming = getRenaming( cnf )
    val renamedCNF = cnf.map( TermReplacement( _, renaming.toMap ) )
    ( renamedCNF, renaming, invertRenaming( renaming ) )
  }
}

object groundFreeVariables {
  def getGroundingMap( vars: Set[Var], consts: Set[Const] ): Seq[( Var, Const )] = {
    val nameGen = rename.awayFrom( consts )
    vars.toSeq map { v => v -> Const( nameGen fresh v.name, v.exptype ) }
  }

  def getGroundingMap( seq: HOLSequent ): Seq[( Var, Const )] =
    getGroundingMap( variables( seq ), constants( seq ) )

  def apply( seq: HOLSequent ): ( HOLSequent, Map[Const, Var] ) = {
    val groundingMap = getGroundingMap( seq )
    val groundSeq = Substitution( groundingMap )( seq )
    val unground = groundingMap.map { case ( f, t ) => ( t, f ) }
    ( groundSeq, unground.toMap )
  }
}