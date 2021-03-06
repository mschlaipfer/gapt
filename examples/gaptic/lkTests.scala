package at.logic.gapt.examples

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.expr._

object lkTests {
  val eqLemma = Lemma(
    Sequent( Seq( "c" -> parseFormula( "P(y) & Q(y)" ), "eq1" -> parseFormula( "u = v" ), "eq2" -> parseFormula( "y = x" ), "a" -> parseFormula( "P(u) -> Q(u)" ) ), Seq( "b" -> parseFormula( "P(x) & Q(x)" ) ) )
  ) {
      eql( "eq1", "a" ) yielding hof"P(v) -> Q(v)"
      eql( "eq1", "a" ) yielding hof"P(v) -> Q(u)"
      eql( "eq2", "b" ).fromRightToLeft
      trivial
    }
}