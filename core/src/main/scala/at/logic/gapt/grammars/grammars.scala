package at.logic.gapt.grammars
import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ BabelExporter, MapBabelSignature }

private class VtratgExporter( unicode: Boolean, vtratg: VectTratGrammar )
    extends BabelExporter( unicode, vtratg.babelSignature ) {

  def csep( docs: List[Doc] ): Doc = ssep( docs, line( ", " ) )

  def export(): String = {
    val ntDecl = group( "Non-terminal vectors:" <> nest( line <> csep(
      vtratg.nonTerminals.toList map { nt =>
        "(" <> hsep( nt map { show( _, false, Set(), Map(), prio.max )._1 }, "," ) <> ")"
      }
    ) ) )

    val tDecl = group( "Terminals:" <> nest( line <> csep(
      vtratg.terminals.toList.sortBy { _.name } map { show( _, false, Set(), Map(), prio.max )._1 }
    ) ) )

    val knownTypes = vtratg.terminals.map { c => c.name -> c }.toMap

    val prods = sep( vtratg.productions.toList
      sortBy { case ( as, ts ) => ( vtratg.nonTerminals.indexOf( as ), ts.toString ) }
      map { p =>
        group( csep( p.zipped map ( ( a, t ) =>
          group( show( a, false, Set(), knownTypes, prio.impl )._1 </> nest( "→" </>
            show( t, true, Set(), knownTypes, prio.impl )._1 ) ) ) ) ) <> line
      } )

    pretty( group( ntDecl <> line <> tDecl <> line <> line <> prods ) )
  }

}

object VectTratGrammar {
  type NonTerminalVect = List[FOLVar]
  type Production = ( NonTerminalVect, List[FOLTerm] )
}

case class VectTratGrammar( axiom: FOLVar, nonTerminals: Seq[VectTratGrammar.NonTerminalVect], productions: Set[VectTratGrammar.Production] ) {
  import VectTratGrammar._

  def axiomVect: NonTerminalVect = List( axiom )

  def productions( nonTerminalVect: NonTerminalVect ): Set[Production] = productions filter ( _._1 == nonTerminalVect )
  def rightHandSides( nonTerminal: NonTerminalVect ) = productions( nonTerminal ) map ( _._2 )

  def terminals: Set[Const] = productions flatMap { p => constants( p._2 ) }

  def babelSignature = MapBabelSignature( terminals )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal vector $a in $p" )
      val i = nonTerminals.indexOf( a )
      val allowedNonTerminals = nonTerminals.drop( i + 1 ).flatten.toSet
      t.flatMap( freeVariables( _ ) ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
      require( a.size == t.size, s"vector production $p has sides of different length" )
  }
  require( nonTerminals contains axiomVect, s"axiom is unknown non-terminal vector $axiom" )

  def size = productions.size

  def language: Set[FOLTerm] = {
    var lang = Set[FOLTerm]( axiom )
    nonTerminals.foreach { a =>
      val P_a = productions( a )
      if ( P_a.nonEmpty )
        lang = P_a.flatMap { p =>
          FOLSubstitution( p.zipped )( lang )
        }
    }
    lang filter ( freeVariables( _ ).isEmpty )
  }

  override def toString: String = new VtratgExporter( unicode = true, vtratg = this ).export()
}

object TratGrammar {
  type Production = ( FOLVar, FOLTerm )

  def asVectTratGrammarProduction( p: Production ): VectTratGrammar.Production =
    List( p._1 ) -> List( p._2 )
}

case class TratGrammar( axiom: FOLVar, nonTerminals: Seq[FOLVar], productions: Set[TratGrammar.Production] ) {
  import TratGrammar._

  private val nLine = sys.props( "line.separator" )

  def productions( nonTerminal: FOLVar ): Set[Production] = productions filter ( _._1 == nonTerminal )
  def rightHandSides( nonTerminal: FOLVar ) = productions( nonTerminal ) map ( _._2 )

  productions foreach {
    case p @ ( a, t ) =>
      require( nonTerminals contains a, s"unknown non-terminal $a in $p" )
      val allowedNonTerminals = nonTerminals.drop( nonTerminals.indexOf( a ) + 1 ).toSet
      freeVariables( t ) foreach { fv =>
        require( allowedNonTerminals contains fv, s"acyclicity violated in $p: $fv not in $allowedNonTerminals" )
      }
  }
  require( nonTerminals contains axiom, s"axiom is unknown non-terminal $axiom" )

  def toVectTratGrammar: VectTratGrammar = VectTratGrammar(
    axiom, nonTerminals map ( List( _ ) ),
    productions map asVectTratGrammarProduction
  )

  def language: Set[FOLTerm] = toVectTratGrammar language

  override def toString: String = {
    val s = new StringBuilder
    s append s"Axiom: $axiom" + nLine
    s append s"Non-terminals: ${nonTerminals.mkString( ", " )}" + nLine
    s append s"Productions:" + nLine
    productions.toSeq.sortBy { case ( a, t ) => ( nonTerminals.indexOf( a ), t.toString ) } foreach {
      case ( a, t ) =>
        s append s"  $a -> $t" + nLine
    }
    s.toString()
  }
}
