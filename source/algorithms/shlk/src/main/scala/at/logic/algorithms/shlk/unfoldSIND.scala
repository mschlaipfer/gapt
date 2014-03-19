// --------------------- substitution begin

package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.slk._

//test version
object applySchemaSubstitution2 {
  def handleSchemaEquivalenceRule ( new_parent: LKProof,
                                    subst: Substitution,
                                    old_parent: LKProof,
                                    old_proof: LKProof,
                                    constructor: (LKProof, SchemaFormula) => LKProof with PrincipalFormulas,
                                    m: FormulaOccurrence
                                    ) = {
    val new_proof = constructor( new_parent, subst(m.formula.asInstanceOf[SchemaFormula]))
    new_proof
  }

  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
  def handleWeakening( new_parent: LKProof,
                       subst: Substitution,
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, SchemaFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
    val new_proof = constructor( new_parent, unfoldSFormula(subst(m.formula.asInstanceOf[SchemaFormula])) )
    new_proof
  }
  def handleContraction( new_parent: LKProof,
                         subst: Substitution,
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         constructor: (LKProof, SchemaFormula) => LKProof) = {

    constructor( new_parent, unfoldSFormula(subst(a1.formula.asInstanceOf[SchemaFormula])) )
  }
  def handleBinaryProp( new_parent_1: LKProof,
                        new_parent_2: LKProof,
                        subst: Substitution,
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, SchemaFormula, SchemaFormula) => LKProof) = {

    constructor( new_parent_1, new_parent_2, unfoldSFormula(subst(a1.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(a2.formula.asInstanceOf[SchemaFormula])) )
  }



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: Substitution ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => 
            unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))), 
          ro.succedent.toList.map(fo => 
            unfoldSFormula(subst(fo.formula.asInstanceOf[SchemaFormula]))))
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m)
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionRightRule.apply)
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        val new_proof = sCutRule( new_p1, new_p2, unfoldSFormula(subst(a1.formula.asInstanceOf[SchemaFormula])) )
        new_proof
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft1Rule( new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(f) ) )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft2Rule( new_parent, unfoldSFormula(subst(f)), unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])) )
        new_proof
      }

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(_, w) => w
          case _ => throw new Exception("Error in OrRight1Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        val new_proof = OrRight1Rule( new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(f) ) )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(w, _) => w
          case _ => throw new Exception("Error in OrRight2Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, unfoldSFormula(subst(f)), unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula]) ) )
        new_proof
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegLeftRule( new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])) )
        new_proof
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegRightRule( new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])) )
        new_proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = new_parents.head
        val new_parent2 = new_parents.last
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(subst(a1.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(a2.formula.asInstanceOf[SchemaFormula])))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = new_parents.head
        ImpRightRule(new_parent, unfoldSFormula(subst(a1.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(a2.formula.asInstanceOf[SchemaFormula])))
      }
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = new_parents.head

        ForallLeftRule(new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(m.formula.asInstanceOf[SchemaFormula])), unfoldSTerm(subst(t.asInstanceOf[SchemaExpression])))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = new_parents.head
        ForallRightRule(new_parent, unfoldSFormula(subst(a.formula.asInstanceOf[SchemaFormula])), unfoldSFormula(subst(m.formula.asInstanceOf[SchemaFormula])), subst(v.asInstanceOf[SchemaVar]).asInstanceOf[SchemaVar])
      }
    }
  }

  //************************************************************************************

  def apply( proof_name: String, number: Int ): LKProof = {
    if (number == 0) {
      CloneLKProof2(SchemaProofDB.get(proof_name).base)
    }
    else {
      val k = IntVar("k")
      val subst = Substitution((k.asInstanceOf[SchemaVar], toIntegerTerm(number-1))::Nil)
      apply(SchemaProofDB.get(proof_name).rec, subst, number)
    }
  }

  def apply( proof: LKProof, subst: Substitution , cnt: Int) : LKProof = {
    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
        val new_ind = subst(ind)
        if (cnt == 0) {
          CloneLKProof2(SchemaProofDB.get(link).base)
        }
        else
        if (cnt == 1) {
          new_ind match {
            case y:IntZero => {
              CloneLKProof2(SchemaProofDB.get(link).base)
            }
            case _ => {
              apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]))
            }
          }
        }
        else {
          if(StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]) == cnt) {
            apply(SchemaProofDB.get(link).rec, subst, cnt)
          }
          else {
            val new_map = (subst.schemamap - subst.schemamap.head._1) + Pair(subst.schemamap.head._1, Pred(new_ind.asInstanceOf[IntegerTerm]) )
            val new_subst = Substitution(new_map)
            apply(SchemaProofDB.get(link).rec, new_subst, cnt-1)
          }
        }
      }

      case AndEquivalenceRule1(up, r, aux, main) =>  {
        val up1 = apply(up, subst, cnt)
        AndEquivalenceRule1(up1, subst(aux.formula.asInstanceOf[SchemaFormula]), subst(main.formula.asInstanceOf[SchemaFormula]))
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
        OrEquivalenceRule1(apply(up, subst, cnt), subst(aux.formula.asInstanceOf[SchemaFormula]), subst(main.formula.asInstanceOf[SchemaFormula]))
      }

      case trsArrowRule(up, r, aux, _) =>  {
        apply(up, subst, cnt)
      }

      case Axiom(_) => {
        val res = handleRule( proof, Nil, subst )
        res
      }
      case UnaryLKProof(_, p, _, _, _) => {
        val res = handleRule( proof, apply( p, subst, cnt )::Nil, subst )
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        val pr1 = apply( p1, subst, cnt )
        val pr2 = apply( p2, subst, cnt )
        val res = handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply)
        res
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        val res = handleRule( proof, apply( p1, subst, cnt )::apply( p2, subst, cnt )::Nil, subst )
        res
      }
      case _ => throw new Exception("ERROR in apply schema substitution\n")
    }
  }
}


//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
//uses t.r.s. !!!
// TODO: there exists a CloneLKProof already in algorithms LK. Why aren't they merged??
object CloneLKProof2 {

  def apply(p: LKProof):LKProof = {
    p match {
      case trsArrowLeftRule(p, s, a, m) => {
        apply(p)
      }
      case trsArrowRightRule(p, s, a, m) => {
        apply(p)
      }

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => unfoldSFormula(fo.formula.asInstanceOf[SchemaFormula])),ro.succedent.map(fo => unfoldSFormula(fo.formula.asInstanceOf[SchemaFormula])))

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        AndLeftEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        AndRightEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        OrRightEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        AndLeftEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        AndRightEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        OrRightEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        WeakeningLeftRule( new_p, unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]) )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
        WeakeningRightRule( new_p, unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]) )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        CutRule(new_p1, new_p2, unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        OrLeftRule(new_p1, new_p2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        AndRightRule(new_p1, new_p2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case NegLeftRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegLeftRule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]) )
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula match { case And(_, right) => right }
        AndLeft1Rule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2))
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        AndLeft2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]) )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        OrRight1Rule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2))
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
        OrRight2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]))
      }

      case NegRightRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegRightRule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]) )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionLeftRule( new_p, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]) )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionRightRule( new_p, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]) )
      }

      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallLeftRule(new_parent, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]), unfoldSTerm(t.asInstanceOf[SchemaVar]))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = apply(p)
        ForallRightRule(new_parent, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]), v)
      }

      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = apply(p1)
        val new_parent2 = apply(p2)
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = apply(p)
        ImpRightRule(new_parent, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }
      case _ => throw new Exception("ERROR in unfolding: CloneLKProof2: missing rule !\n")
    }}
}

//removes the arrow rules and unfolds the sTerms
//the proof does not contain proof-links
object LKrwToLK {
  def apply(p: LKProof): LKProof = {
    p match {
      case Axiom(seq) => Axiom(seq.antecedent.map(f => unfoldSFormula(f.formula.asInstanceOf[SchemaFormula])), seq.succedent.map(f => unfoldSFormula(f.formula.asInstanceOf[SchemaFormula])))
      case trsArrowLeftRule(p, s, a, m) => {
        apply(p)
      }
      case trsArrowRightRule(p, s, a, m) => {
        apply(p)
      }
      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        WeakeningLeftRule( new_p, unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]) )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
        WeakeningRightRule( new_p, unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]) )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        CutRule(new_p1, new_p2, unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        OrLeftRule(new_p1, new_p2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        AndRightRule(new_p1, new_p2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }

      case NegLeftRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegLeftRule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]))
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, right) => right }
        AndLeft1Rule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2))
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        AndLeft2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]) )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        OrRight1Rule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2))
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
        OrRight2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]))
      }

      case NegRightRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegRightRule( new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]) )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionLeftRule( new_p, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]) )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionRightRule( new_p, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]) )
      }
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallLeftRule(new_parent, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]), unfoldSTerm(t.asInstanceOf[SchemaVar]))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = apply(p)
        ForallRightRule(new_parent, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]), v)
      }

      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = apply(p1)
        val new_parent2 = apply(p2)
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = apply(p)
        ImpRightRule(new_parent, unfoldSFormula(a1.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(a2.formula.asInstanceOf[SchemaFormula]))
      }
      case _ => throw new Exception("ERROR in rewriting: LKrwToLK: missing rule !\n"+p.rule) 
    }
  }
}
