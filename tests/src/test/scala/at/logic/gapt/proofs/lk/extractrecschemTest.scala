package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.{ tapeUrban, tape, Pi2Pigeonhole }
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.grammars.{ RecursionScheme, Rule }
import at.logic.gapt.proofs.{ Ant, HOLSequent, Sequent, Suc }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

class ExtractRecSchemTest extends Specification with SatMatchers {
  "simple" in {
    val P = FOLAtomConst( "P", 1 )
    val c = FOLConst( "c" )
    val f = FOLFunctionConst( "f", 1 )
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val z = FOLVar( "z" )

    val g0 = P( c )
    val g1 = All( y, P( y ) --> P( f( y ) ) )
    val g2 = P( f( f( f( f( c ) ) ) ) )

    val p1 = solve.solvePropositional(
      ( P( x ) --> P( f( x ) ) ) +:
        ( P( f( x ) ) --> P( f( f( x ) ) ) ) +:
        Sequent()
        :+ ( P( x ) --> P( f( f( x ) ) ) )
    ).get
    val cutf = All( z, P( z ) --> P( f( f( z ) ) ) )
    val p2 = ForallLeftRule( p1, g1, x )
    val p3 = ForallLeftRule( p2, g1, f( x ) )
    val p4 = ContractionMacroRule( p3 )
    val p5 = ForallRightRule( p4, cutf, x )

    val q1 = solve.solvePropositional(
      ( P( c ) --> P( f( f( c ) ) ) ) +:
        ( P( f( f( c ) ) ) --> P( f( f( f( f( c ) ) ) ) ) ) +:
        Sequent()
        :+ ( P( c ) --> P( f( f( f( f( c ) ) ) ) ) )
    ).get
    val q2 = ForallLeftRule( q1, cutf, c )
    val q3 = ForallLeftRule( q2, cutf, f( f( c ) ) )
    val q4 = ContractionMacroRule( q3 )

    val p = CutRule( p5, q4, cutf )

    val recSchem = extractRecSchem( p )
    val lang = recSchem.language.map( _.asInstanceOf[HOLFormula] )

    Sat4j.isValid( Sequent() :++ lang ) must beTrue
  }

  "bottom" in { Or( extractRecSchem( BottomAxiom ).language.map { _.asInstanceOf[HOLFormula] } ) must beValid }
  "top" in { Or( extractRecSchem( TopAxiom ).language.map { _.asInstanceOf[HOLFormula] } ) must beValid }

  "pi2 pigeonhole" in {
    val p = Pi2Pigeonhole.proof
    val recSchem = extractRecSchem( p )

    val lang = recSchem.language.map( _.asInstanceOf[HOLFormula] )

    Escargot isValid ( Sequent() :++ lang ) must beTrue
  }

  "tape proof" in {
    val proof = DefinitionElimination( tape.defs )( tape.p )

    val recSchem = extractRecSchem( proof )
    val lang = recSchem.language.map( _.asInstanceOf[HOLFormula] )
    Escargot isValid ( Sequent() :++ lang ) must_== true

    val recSchemWithEq = extractRecSchem( proof, includeEqTheory = true )
    val langWithEq = recSchemWithEq.language.map( _.asInstanceOf[HOLFormula] )
    Or( langWithEq ) must beValid
  }

  "urban tape proof" in {
    val proof = DefinitionElimination( tapeUrban.defs )( tapeUrban.sigma )

    val recSchem = extractRecSchem( proof )
    val lang = recSchem.language.map( _.asInstanceOf[HOLFormula] )
    Escargot isValid ( Sequent() :++ lang ) must_== true
  }

  "simple pi3" in {
    val P = FOLAtomConst( "P", 3 )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val Seq( x, y, z, w1, w2, w3 ) = Seq( "x", "y", "z", "w1", "w2", "w3" ) map { FOLVar( _ ) }

    val cutf = All( x, Ex( y, All( z, P( x, y, z ) ) ) )

    var p1: LKProof = LogicalAxiom( P( w1, w1, w2 ) )
    p1 = ForallLeftBlock( p1, All( x, All( y, P( x, x, y ) ) ), Seq( w1, w2 ) )
    p1 = ForallRightRule( p1, instantiate( cutf, Seq( w1, w1 ) ), w2 )
    p1 = ExistsRightRule( p1, instantiate( cutf, w1 ), w1 )
    p1 = ForallRightRule( p1, cutf, w1 )

    var p2: LKProof = LogicalAxiom( P( c, w3, d ) )
    p2 = ExistsRightRule( p2, Ex( x, P( c, x, d ) ), w3 )
    p2 = ForallLeftRule( p2, instantiate( cutf, Seq( c, w3 ) ), d )
    p2 = ExistsLeftRule( p2, instantiate( cutf, c ), w3 )
    p2 = ForallLeftRule( p2, cutf, c )

    val p = CutRule( p1, p2, cutf )

    val recschem = extractRecSchem( p )
    // println( recschem )
    // recschem.language foreach println
    recschem.rules map {
      case Rule( HOLAtom( head, _ ), _ ) => head
    } foreach {
      case Const( name, ty ) =>
      // println( s"$name: $ty" )
    }

    Or( recschem.language.map( _.asInstanceOf[FOLFormula] ) ) must beValid
  }

  "numeral induction" in {
    val nat = TBase( "Nat" )
    val o = Const( "Zero", nat )
    val s = Const( "Suc", nat -> nat )

    val witness = TBase( "Witness" )
    val p = HOLAtomConst( "p", nat, witness )
    val g = Const( "g", witness -> witness )
    val c = Const( "c", witness )
    val x = Var( "x", nat )
    val y = Var( "y", witness )

    val proof = ( ProofBuilder
      c LogicalAxiom( p( o, y ) )
      u ( ForallLeftRule( _, All( y, p( o, y ) ), y ) )
      u ( ForallRightRule( _, All( y, p( o, y ) ) ) )

      c LogicalAxiom( p( x, g( y ) ) )
      c LogicalAxiom( p( s( x ), y ) )
      b ( ImpLeftRule( _, Suc( 0 ), _, Ant( 0 ) ) )
      u ( ForallLeftBlock( _, All( x, All( y, p( x, g( y ) ) --> p( s( x ), y ) ) ), Seq( x, y ) ) )
      u ( ForallLeftRule( _, All( y, p( x, y ) ), g( y ) ) )
      u ( ForallRightRule( _, All( y, p( s( x ), y ) ) ) )

      b { ( base, step ) =>
        val baseCase = InductionCase( base, o, Seq(), Seq(), Suc( 0 ) )
        val stepCase = InductionCase( step, s, Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) )
        InductionRule( Seq( baseCase, stepCase ), All( x, All( y, p( x, y ) ) ) )
      }

      c LogicalAxiom( p( x, c ) )
      u ( ForallLeftBlock( _, All( x, All( y, p( x, y ) ) ), Seq( x, c ) ) )

      b ( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) ) qed )

    val recSchem = extractRecSchem( proof )
    Or( recSchem.parametricLanguage( s( s( o ) ) ) map { _.asInstanceOf[HOLFormula] } ) must beValid
  }
}

class Pi2FactorialPOC extends Specification {
  val A = Const( "A", Ti -> To )
  val B = Const( "B", Ti -> ( Ti -> ( ( Ti -> To ) -> To ) ) )
  val C = Const( "C", Ti -> To )
  val D = Const( "D", ( Ti -> To ) -> ( Ti -> ( Ti -> ( Ti -> To ) ) ) )

  val O = Const( "0", Ti )
  val s = Const( "s", Ti -> Ti )
  val plus = Const( "+", Ti -> ( Ti -> Ti ) )
  val times = Const( "*", Ti -> ( Ti -> Ti ) )
  val g = Const( "g", Ti -> ( Ti -> Ti ) )
  val f = Const( "f", Ti -> Ti )

  val X = Var( "X", Ti -> To )
  val x = Var( "x", Ti )
  val y = Var( "y", Ti )
  val z = Var( "z", Ti )
  val w = Var( "w", Ti )

  val hors = RecursionScheme(
    A,
    Set( A, B, C, D ),

    A( z ) -> B( z, s( O ), C ),
    A( z ) -> Eq( times( s( O ), z ), z ),
    A( z ) -> Neg( Eq( f( z ), g( s( O ), z ) ) ),
    B( s( x ), y, X ) -> B( x, times( y, s( x ) ), D( X, x, y ) ),
    D( X, x, y, w ) -> Eq( times( times( y, s( x ) ), w ), times( y, times( s( x ), w ) ) ),
    D( X, x, y, w ) -> Eq( g( y, s( x ) ), g( times( y, s( x ) ), x ) ),
    D( X, x, y, w ) -> Eq( f( s( x ) ), times( s( x ), f( x ) ) ),
    D( X, x, y, w ) -> X( times( s( x ), w ) ),
    B( O, y, X ) -> Eq( g( y, O ), y ),
    B( O, y, X ) -> Eq( f( O ), s( O ) ),
    B( O, y, X ) -> Eq( times( s( O ), s( O ) ), s( O ) ),
    B( O, y, X ) -> X( s( O ) )
  )

  def lang( i: Int ) = hors.parametricLanguage( Numeral( i ) ).map( _.asInstanceOf[HOLFormula] )

  // println( hors )
  // println()
  // lang( 3 ).toSeq.sortBy( _.toString ) foreach println
  // println()

  "termination" in {
    lang( 10 )
    ok
  }

  "languages should be tautologies" in {
    Fragment.foreach( 0 to 7 ) { i =>
      s"n = $i" in {
        Escargot isValid ( lang( i ) ++: Sequent() ) must beTrue
      }
    }
  }
}