package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.tptp.TPTPHOLExporter
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.fol.{ reduceHolToFol, replaceAbstractions, undoHol2Fol }
import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.ceres.subsumedClausesRemoval
import at.logic.gapt.proofs.lksk.{ LKskProof, LKskToExpansionProof }
import at.logic.gapt.proofs.{ HOLClause, Sequent }
import at.logic.gapt.proofs.ceres_omega._
import at.logic.gapt.proofs.resolution.{ Robinson2RalWithAbstractions, RobinsonToLK }
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.{ TimeOutException, withTimeout }

import scala.concurrent.duration.Duration

/**
 * The generic template for the nTape proofs.
 */
abstract class nTape {
  /** The proof database to start from. */
  def proofdb(): ExtendedProofDatabase

  /** The name of the root proof to start with */
  def root_proof(): String

  /**
   * Timeout for call to theorem provers.
   *
   * @return the timeout as duration. default: 60 seconds
   */
  def timeout(): Duration = Duration( "10s" )

  /**
   * The input LK proof, extracted by the name [[root_proof]] from the proof database ([[proofdb]])
   */
  lazy val input_proof = proofdb proof root_proof

  /**
   * The input proof (TAPEPROOF) after preprocessing step 1: definition elimination
   */
  lazy val preprocessed_input_proof1 = DefinitionElimination( proofdb.Definitions )( input_proof )

  /**
   * The input proof after preprocessing step 2: expansion of logical axioms to atomic axioms
   */
  lazy val preprocessed_input_proof2 = AtomicExpansion( preprocessed_input_proof1 )

  /**
   * The input proof preprocessing step 3: regularization
   */
  lazy val preprocessed_input_proof3 = regularize( preprocessed_input_proof2 )

  /**
   * The input proof (TAPEPROOF) after definition elimination([[preprocessed_input_proof1]], expansion of logical axioms
   * to atomic axioms ([[preprocessed_input_proof2]]) and regularization ([[preprocessed_input_proof3]])
   */
  lazy val preprocessed_input_proof = preprocessed_input_proof3

  /**
   * The processed input proof converted to LKsk.
   */
  lazy val lksk_proof = LKToLKsk( preprocessed_input_proof )

  /**
   * The struct of the proof. It is an intermediate representation of the characteristic sequent set.
   */
  lazy val struct = extractStructFromLKsk( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The set of projections of the [[preprocessed_input_proof]].
   */
  lazy val projections = Projections( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The characteristic sequent set of the [[preprocessed_input_proof]].
   */
  lazy val css = StandardClauseSet( struct )

  /**
   * The characteristic sequent set ([[css]]) after removal of labels and subsumption
   */
  lazy val preprocessed_css = {
    val stripped_css = css.map( _.map( LKskProof.getFormula ) )
    subsumedClausesRemoval( stripped_css.toList )
  }

  /**
   * The first order export of the preprocessed characteristic sequent set ([[preprocessed_css]]), together with the map of
   * replacing constants.
   */
  lazy val ( abstracted_constants_map, fol_css ) = {
    val css_nolabels = preprocessed_css // remove labels from css
    val ( abs_consts, abs_css ) = replaceAbstractions( css_nolabels )
    /* map types to first order*/
    val fol_css = reduceHolToFol( abs_css )
    /* converting to clause form, this is cleaner than casting */
    val fol_ccs = fol_css map {
      case Sequent( ant, succ ) =>
        HOLClause(
          ant map { case atom @ FOLAtom( _, _ ) => atom },
          succ map { case atom @ FOLAtom( _, _ ) => atom }
        )
    }
    ( abs_consts, fol_ccs )
  }

  /**
   * The first order refutation of the first order characteristic sequent set ([[fol_css]])
   */
  lazy val fol_refutation = {
    val some_rp = try {
      val css = fol_css //evaluate lazy val, otherwise the thread stays blocked
      withTimeout( timeout() ) { Prover9.getRobinsonProof( css ) }
    } catch {
      case e: TimeOutException =>
        println( s"Could not refute the clause set within ${timeout()}." )
        throw e
    }

    some_rp match {
      case None =>
        throw new Exception( "Could not refute clause set!" )
      case Some( rp ) =>
        rp
    }
  }

  /**
   * The expansion proof of the first-order refutation ([[fol_refutation]]).
   */
  lazy val fol_refutation_expansion_proof = {
    val end_sequent = Sequent( fol_css.map( x => univclosure( x.toDisjunction ) ), Nil )
    val lk_rp = RobinsonToLK( fol_refutation, end_sequent )
    LKToExpansionProof( lk_rp )
  }

  /**
   * Exports the preprocessed characteristic sequent ([[preprocessed_css]]) set to the TPTP THF format
   *
   * @param filename The name of the file to export to
   */
  def export_thf( filename: String ): Unit = {
    TPTPHOLExporter( preprocessed_css, filename, false )
  }

  /**
   * The ral version of the first-order refutation ([[fol_refutation]]), with all necessary simplifications undone
   */
  lazy val ral_refutation = {
    val signature = undoHol2Fol.getSignature( lksk_proof, LKskProof.getFormula )

    val converter = Robinson2RalWithAbstractions( signature, abstracted_constants_map )

    converter( fol_refutation )
  }

  /**
   * The simulation of the [[ral_refutation]] on the [[projections]] i.e. an LKsk proof where cuts only work on atom formulas
   */
  lazy val acnf = ceres_omega( projections, ral_refutation, lksk_proof.conclusion, struct )._1

  /**
   * The expansion proof of the cut-free proof [[acnf]].
   */
  lazy val expansion_proof = LKskToExpansionProof( acnf )

  /**
   * A first-order conversion of the deep formula of the [[expansion_proof]].
   */
  lazy val expansion_proof_fol_deep = reduceHolToFol( replaceAbstractions( expansion_proof.expansionSequent.deep.toImplication ) )

  /**
   * The proof of the deep formula of the [[expansion_proof]].
   */
  lazy val reproved_deep = {
    EProver getRobinsonProof expansion_proof_fol_deep match {
      case None      => throw new Exception( "Could not reprove deep formula!" )
      case Some( p ) => p
    }
  }

  //prints the interesting terms from the expansion sequent
  def printStatistics() = {
    println( "------------ Proof sizes --------------" )
    println( s"Input proof            : ${input_proof.treeLike.size}" )
    println( s"Preprocessed input     : ${preprocessed_input_proof.treeLike.size}" )
    println( s"LKsk input proof       : ${lksk_proof.treeLike.size}" )
    println( s"ACNF output proof      : ${acnf.treeLike.size}" )
    println( "------------ " )
    println( s"Css size               : ${css.size}" )
    println( s"Preprocessed css size  : ${preprocessed_css.size}" )
    println( "------------ " )
    println( s"Refutation size (dag)  : ${fol_refutation.dagLike.size}" )
    println( s"Refutation size (tree) : ${fol_refutation.treeLike.size}" )
    println( s"Refutation depth       : ${fol_refutation.depth}" )
    println( "------------ " )
    println( s"Reproved deep formula proof size (dag)  : ${reproved_deep.dagLike.size}" )
    println( s"Reproved deep formula proof size (tree) : ${reproved_deep.treeLike.size}" )
    println( "------------ Witness Terms from Expansion Proof --------------" )

    //FIXME: we are using the induction axiom to find its expansion tree now, but antecedent(1) is still not perfect
    val conjuncts = decompose( expansion_proof.expansionSequent.antecedent( 1 ) )
    val ind_atom = HOLAtom( Const( "IND", To ), List() )
    val ind_axiom = proofdb.Definitions.find( _._1 == ind_atom ).get._2
    val indet = conjuncts.find( _.shallow == ind_axiom ).get

    val List( ind1, ind2 ): List[ExpansionTree] = indet match {
      case ETWeakQuantifier( _, instances ) =>
        instances.map( _._2 ).toList
    }

    val ( ind1base, ind1step ) = ind1 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    val ( ind2base, ind2step ) = ind2 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    ( ind1base, ind1step, ind2base, ind2step ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        val map = Map[LambdaExpression, String]()
        val counter = new {
          private var state = 0;

          def nextId = {
            state = state + 1; state
          }
        }

        val ( map1, sb1 ) = replaceAbstractions( sb, map, counter )
        val ( map2, ss1 ) = replaceAbstractions( ss, map1, counter )
        val ( map3, tb1 ) = replaceAbstractions( tb, map2, counter )
        val ( map4, ts1 ) = replaceAbstractions( ts, map3, counter )

        println( "base 1 simplified: " + Abs( xb, sb1 ) )
        println( "base 2 simplified: " + Abs( yb, tb1 ) )
        println( "step 1 simplified: " + Abs( xs, ss1 ) )
        println( "step 2 simplified: " + Abs( ys, ts1 ) )

        println( "With shortcuts:" )
        for ( ( term, sym ) <- map4 ) {
          println( "Symbol: " + sym )
          println( "Term:   " + term )
        }
    }

  }

  /**
   * Prints the preprocessed characteristic sequent set in TPTP THF format. Use [[export_thf]] to write it to a file.
   */
  def print_css_thf(): Unit = {
    println( TPTPHOLExporter( preprocessed_css, false ) )
  }

  private def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }

}
