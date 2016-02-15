package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.gaptic.tactics._
import at.logic.gapt.proofs.lk.LKProof

package object gaptic {
  // LK Tactics

  def axiomLog( l: String ) = new LogicalAxiomTactic( Option( l ) )

  def axiomLog = new LogicalAxiomTactic()

  def axiomTop = TopAxiomTactic

  def axiomBot = BottomAxiomTactic

  def axiomRefl = ReflexivityAxiomTactic

  def axiomTh = TheoryAxiomTactic

  def axiom = AxiomTactic

  def negL( applyToLabel: String ) = new NegLeftTactic( Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def negL = new NegLeftTactic()

  def negR( applyToLabel: String ) = new NegRightTactic( Some( applyToLabel ) )

  def negR = new NegRightTactic()

  def andL( applyToLabel: String ) = new AndLeftTactic( Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def andL = new AndLeftTactic()

  def andR( applyToLabel: String ) = new AndRightTactic( Some( applyToLabel ) )

  def andR = new AndRightTactic()

  def orL( applyToLabel: String ) = new OrLeftTactic( Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def orL = new OrLeftTactic()

  def orR( applyToLabel: String ) = new OrRightTactic( Some( applyToLabel ) )

  def orR = new OrRightTactic()

  def impL( applyToLabel: String ) = new ImpLeftTactic( Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def impL = new ImpLeftTactic()

  def impR( applyToLabel: String ) = new ImpRightTactic( Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def impR = new ImpRightTactic()

  def exL( eigenVariable: Var, applyToLabel: String ) = new ExistsLeftTactic( Some( eigenVariable ), Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def exL( eigenVariable: Var ) = new ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

  def exL( applyToLabel: String ) = new ExistsLeftTactic( applyToLabel = Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def exL = new ExistsLeftTactic()

  def exR( term: LambdaExpression, applyToLabel: String ) = new ExistsRightTactic( term, Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def exR( term: LambdaExpression ) = new ExistsRightTactic( term )

  def allL( term: LambdaExpression, applyToLabel: String ) = new ForallLeftTactic( term, Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def allL( term: LambdaExpression ) = new ForallLeftTactic( term )

  def allR( eigenVariable: Var, applyToLabel: String ) = new ForallRightTactic( Some( eigenVariable ), Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def allR( eigenVariable: Var ) = new ForallRightTactic( eigenVariable = Some( eigenVariable ) )

  def allR( applyToLabel: String ) = new ForallRightTactic( applyToLabel = Some( applyToLabel ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def allR = new ForallRightTactic()

  def cut( h: HOLFormula, c: String ) = CutTactic( h, c )

  def eqL( eq: String, fm: String ) = EqualityLeftTactic( eq, fm )

  def eqR( eq: String, fm: String ) = EqualityRightTactic( eq, fm )

  def defL( l: String, defi: (Const, LambdaExpression), pos: Option[Seq[HOLPosition]] = None ) = DefinitionLeftTactic( l, defi, pos )

  def defR( l: String, defi: (Const, LambdaExpression), pos: Option[Seq[HOLPosition]] = None ) = DefinitionRightTactic( l, defi, pos )

  // Meta

  def insert( proof: LKProof ) = InsertTactic( proof )

  def repeat( t: Tactical ) = RepeatTactic( t )

  // Complex

  def decompose = DecomposeTactic

  def destruct( l: String ) = new DestructTactic( Some( l ) )

  @deprecated( "Please specify a label.  Otherwise the tactic breaks easily with changes in GAPT.", "2016-01-28" )
  def destruct = new DestructTactic()

  def chain( h: String ) = ChainTactic( h )

  def prop = PropTactic

  def prover9 = Prover9Tactic
  def escargot = EscargotTactic

  /**
   * Lets you "forget" a sequence of formulas, i.e. the tactics version of the weakening rule.
   * @param ls A sequence of labels L,,1,,,..., L,,n,,.
   * @return The tactical
   *           (WeakeningLeftTactic(L,,1,,) orElse WeakeningRightTactic(L,,1,,)) andThen ... andThen (WeakeningLeftTactic(L,,n,,) orElse WeakeningRightTactic(L,,n,,))
   *
   */
  def forget( ls: String* ): Tactical = ls.foldLeft[Tactical]( SkipTactical ) { ( acc, l ) =>
    acc andThen ( WeakeningLeftTactic( l ) orElse WeakeningRightTactic( l ) )
  }

  def paramod( l: String, axiom: HOLAtom, target: HOLFormula ) = ParamodulationTactic( l, axiom, target )

  def rewrite = RewriteTactic( equations = Seq(), target = None, once = true )
}
