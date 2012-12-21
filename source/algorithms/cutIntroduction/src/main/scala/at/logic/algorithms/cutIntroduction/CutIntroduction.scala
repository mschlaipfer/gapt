/**
 * Cut introduction algorithm
 * 
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.occurrences._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import at.logic.algorithms.lk._
import at.logic.algorithms.shlk._
import at.logic.algorithms.interpolation._
import at.logic.algorithms.resolution._
import at.logic.calculi.resolution.base.FClause

class CutIntroException(msg: String) extends Exception(msg)

object CutIntroduction {

  def apply(proof: LKProof) : Option[LKProof] = {

    val endSequent = proof.root
    println("\nEnd sequent: " + endSequent)

    // Extract the terms used to instantiate each formula
    val termsTuples = TermsExtraction(proof)

    // Assign a fresh function symbol to each quantified formula in order to
    // transform tuples into terms.
    val flatterms = new FlatTermSet(termsTuples)
    val terms = flatterms.termset
    val formulaFunctionSymbol = flatterms.formulaFunction

    println("\nTerm set: {" + terms + "}")
    println("of size " + terms.size)

    val decompositions = Decomposition(terms).sortWith((d1, d2) =>
      d1._1.length + d1._2.length < d2._1.length + d2._2.length
    )

    println("Number of decompositions in total: " + decompositions.length)

    //decompositions.foreach(d =>
    //  if(d._1.size + d._2.size < terms.size)
    //    println(d._1 + " o " + d._2)
    //)

    if(decompositions.length == 0) {
      println("\nNo decompositions found." + 
        " The proof cannot be compressed using a cut with one universal quantifier.\n")
      return None
    }

    // TODO: how to choose the best decomposition?
    val smallestDec = decompositions.head
    // This is a map from formula occurrence to a list of terms
    val u = smallestDec._1
    // This is a list of terms
    val s = smallestDec._2

    println("\nDecomposition chosen: {" + smallestDec._1 + "} o {" + smallestDec._2 + "}")

    val ehs = new ExtendedHerbrandSequent(endSequent, smallestDec, flatterms)
    
    // Building up the final proof with cut
    println("\nGenerating final proof with cut...\n")
    
    //val cutFormula0 = AllVar(xvar, conj)
    val cutFormula = ehs.canonicalSol

/* TODO: uncomment when fixed.
    // Computing the interpolant (transform this into a separate function later)
    
    // A[s_i] forall i
    val asi = s.map(t => cutFormula0.substitute(t))
    val cutConj = andN(asi)

    // Negative part
    val gamma = ehs.inst_l
    val delta = ehs.inst_r
    val npart = gamma ++ delta

    // Positive part
    val pi = ehs.prop_l :+ cutConj
    val lambda = ehs.prop_r
    val ppart = pi ++ lambda

    // Proof
    val interpProof = solvePropositional(FSequent(gamma++pi, delta++lambda))

    // Getting the formula occurrences...
    val occurrences = interpProof.root.antecedent ++ interpProof.root.succedent
    val npart_occ = occurrences.filter(x => npart.contains(x.formula))
    val ppart_occ = occurrences.filter(x => ppart.contains(x.formula))

    val interpolant = ExtractInterpolant(interpProof, npart_occ.toSet, ppart_occ.toSet)

    println("Interpolant: " + interpolant.toPrettyString + "\n")

    // Adding interpolant to cut formula
    // TODO: casting does not work here.
    val cutFormula = AllVar(xvar, And(conj, interpolant.asInstanceOf[FOLFormula]))
*/

    val alpha = FOLVar(new VariableStringSymbol("α"))
    val cutLeft = cutFormula.substitute(alpha)
    val cutRight = s.foldRight(List[FOLFormula]()) { case (t, acc) =>
      cutFormula.substitute(t) :: acc
    }

    val proofLeft = solvePropositional(FSequent((ehs.inst_l ++ ehs.prop_l), (cutLeft +: (ehs.prop_r ++ ehs.inst_r))))
    val leftBranch = proofLeft match {
      case Some(proofLeft1) => ForallRightRule(uPart(u, proofLeft1, flatterms), cutLeft, cutFormula, alpha)
      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    val proofRight = solvePropositional(FSequent(cutRight ++ ehs.prop_l, ehs.prop_r))
    val rightBranch = proofRight match {
      case Some(proofRight1) => sPart(cutFormula, s, proofRight1)
      case None => throw new CutIntroException("ERROR: propositional part is not provable.")
    }

    val untilCut = CutRule(leftBranch, rightBranch, cutFormula)

    // Contracting the end sequent formulas that are propositional (they go to
    // both branches when the cut is applied)

    val contractAnt = endSequent.antecedent.foldRight(untilCut.asInstanceOf[LKProof]) { case (f, premise) =>
      if(!f.formula.containsQuantifier) {
        ContractionLeftRule(premise, f.formula.asInstanceOf[FOLFormula])
      }
      else premise
    }

    val finalProof = endSequent.succedent.foldRight(contractAnt.asInstanceOf[LKProof]) { case (f, premise) =>
      if(!f.formula.containsQuantifier) {
        ContractionRightRule(premise, f.formula.asInstanceOf[FOLFormula])
      }
      else premise
    }

    Some(CleanStructuralRules(finalProof))
  }

  // Both methods bellow are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules(f: FOLFormula, lst: List[FOLTerm], ax: LKProof) : LKProof = (f, lst) match {
    case (_, Nil) => ax
    case (AllVar(_,_), h::t) => 
      val newForm = f.substitute(h)
      ForallLeftRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
    case (ExVar(_,_), h::t) =>
      val newForm = f.substitute(h)
      ExistsRightRule(genWeakQuantRules(newForm, t, ax), newForm, f, h)
  }
  def uPart(u: List[FOLTerm], ax: LKProof, flatterms: FlatTermSet) : LKProof = {
    u.foldRight(ax) {
      case (term, ax) => 
        var first = true;
        val terms = flatterms.getTermTuple(term)
        val f = flatterms.getFormula(term)
        f.formula.asInstanceOf[FOLFormula] match { 
          case AllVar(_, _) =>
            if(first) {
              first = false
              genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
            }
            else
              ContractionLeftRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
          case ExVar(_, _) =>
            if(first) {
              first = false
              genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax)
            }
            else
              ContractionRightRule(genWeakQuantRules(f.formula.asInstanceOf[FOLFormula], terms, ax), f.formula.asInstanceOf[FOLFormula])
        }
    }
  }

  // Generates the proof derivation where the cut formula is instantiated with
  // the terms from S
  def sPart(cf: FOLFormula, s: List[FOLTerm], p: LKProof) = {
    var first = true;
    s.foldRight(p) { case (t, p) =>
      if(first) {
        first = false
        val scf = cf.substitute(t)
        ForallLeftRule(p, scf, cf, t)
      }
      else {
        val scf = cf.substitute(t)
        ContractionLeftRule(ForallLeftRule(p, scf, cf, t), cf)
      }
    }
  }

  //------------------------ FORGETFUL RESOLUTION -------------------------//

  class MyFClause(val pos: List[FOLFormula], val neg: List[FOLFormula])
 
  def toMyFClause(c: FClause) = {
    val neg = c.neg.toList.map(x => x.asInstanceOf[FOLFormula])
    val pos = c.pos.toList.map(x => x.asInstanceOf[FOLFormula])
    new MyFClause(neg, pos)
  }

  // We assume f is in CNF. Maybe it works also for f not
  // in CNF (since CNFp transforms f to CNF?).
  //
  // Implements forgetful resolution.
  def ForgetfulResolve(f: FOLFormula) : List[FOLFormula] =
  {
    val clauses = CNFp(f).map(c => toMyFClause(c))
    clauses.foldLeft(List[FOLFormula]())( (list, c1) => 
      list ::: clauses.dropWhile( _ != c1).foldLeft(List[FOLFormula]())( (list2, c2) => 
        if (resolvable(c1, c2))
          CNFtoFormula( (clauses.filterNot(c => c == c1 || c == c2 ) + resolve(c1, c2)).toList )::list2
        else
          list2
      )
    )
  }

  // assume (for simplicity) that 
  // cls is not empty, and does not contain the empty
  // clause
  def CNFtoFormula( cls : List[MyFClause] ) : FOLFormula =
  {
    andN(cls.map( c => orN(c.pos ++ c.neg.map( l => l)) ))
  }

  // Checks if complementary literals exist.
  def resolvable(l: MyFClause, r: MyFClause) =
    l.pos.exists( f => r.neg.contains(f) ) || l.neg.exists(f => r.pos.contains(f))

  // Assumes that resolvable(l, r). Does propositional resolution.
  // TODO: incorporate contraction.
  def resolve(l: MyFClause, r: MyFClause) : MyFClause =
  {
    val cl = l.pos.find( f => r.neg.contains(f) )
    if (cl != None)
      new MyFClause( l.neg ++ (r.neg - cl.get) , (l.pos - cl.get) ++ r.pos )
    else
    {
      val cr = l.neg.find( f => r.pos.contains(f) ).get
      new MyFClause( (l.neg - cr) ++ r.neg, l.pos ++ (r.pos - cr) )
    }
  }
  
  //-----------------------------------------------------------------------//

  // TODO: not beeing used currently
  // The canonical solution computed already has only the quantified formulas 
  // from the end-sequent (propositional part is ignored).
  //
  // returns the list of improved solutions found by the forgetful resolution
  // algorithm.
  def improveSolution(sol: FOLFormula, ehs: ExtendedHerbrandSequent) : List[FOLFormula] = {

    // Remove quantifier 
    val (x, f) = sol match {
      case AllVar(x, form) => (x, form)
      case _ => throw new CutIntroException("ERROR: Canonical solution is not quantified.")
    }

    // Transform to conjunctive normal form
    val cnf = f.toCNF

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: ForgetfulResolve(f).foldRight(List[FOLFormula]()) ( (r, acc) => 
          // Should I insert this quantifier by hand?
          if(ehs.isValidWith(AllVar(x,r))) {
            searchSolution(r) ::: acc
          }
          else acc
        )

    searchSolution(cnf)
  }

  def minimalImprovedSolution(sol: FOLFormula, ehs: ExtendedHerbrandSequent) : FOLFormula =
    improveSolution(sol, ehs).sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head

}
