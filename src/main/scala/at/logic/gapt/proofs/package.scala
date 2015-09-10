package at.logic.gapt

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr._

package object proofs {

  type HOLSequent = Sequent[HOLFormula]

  implicit class RichFormulaSequent( val sequent: Sequent[HOLFormula] ) {
    def formulas = sequent.elements
    def polarizedFormulas = sequent.polarizedElements

    /**
     * Interpretation of the sequent as a formula.
     * Why is this not the definition of a sequent (/\ F -> \/ G)? The current implementation (\/-F \/ G) is
     * only classically equivalent (In IL a -> b :/- -a \/ b).
     */
    def toFormula: HOLFormula = Or( sequent.antecedent.toList.map( f => Neg( f ) ) ++ sequent.succedent )

    def toNegFormula: HOLFormula = And( sequent.antecedent ++ sequent.succedent.map( Neg( _ ) ) )

    def toImplication: HOLFormula = Imp( And( sequent.antecedent.toList ), Or( sequent.succedent ) )

    def renameSymbols( map: SymbolMap ) = sequent map ( NameReplacement( _, map ) )
  }

  object HOLSequent {
    def apply(): HOLSequent = Sequent()
    def apply( ant: Seq[HOLFormula], succ: Seq[HOLFormula] ): HOLSequent = Sequent( ant, succ )
    def apply( polarizedElements: Seq[( HOLFormula, Boolean )] ): HOLSequent = Sequent( polarizedElements )
    def unapply( f: HOLSequent ): Option[( Seq[HOLFormula], Seq[HOLFormula] )] = Some( ( f.antecedent, f.succedent ) )
  }

  type Clause[+A] = Sequent[A]

  type HOLClause = Clause[HOLAtom]
  type FOLClause = Clause[FOLAtom]

  implicit class RichClause[+A]( val clause: Clause[A] ) {
    def negative = clause.antecedent
    def positive = clause.succedent

    def literals = ( negative map { f => ( f, false ) } ) ++ ( positive map { f => ( f, true ) } )
  }
}
