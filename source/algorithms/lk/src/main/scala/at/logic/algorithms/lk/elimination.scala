package at.logic.algorithms.lk

import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol._
import at.logic.language.schema.{And => AndS, Or => OrS, SchemaFormula}
import at.logic.calculi.slk._

/**
 * Removes the redundant weakenings and contractions.
 * Linear algorithm. Traverses the proof top down, keeping track of the
 * weakened formulas. Checks if the auxiliary formulas of each rule are weakened
 * or not and treats it appropriately.
 * TODO: make it tail-recursive.
 */
object CleanStructuralRules {

<<<<<<< .working
  private def applyRec(proof: LKProof, forms: Iterable[FormulaOccurrence]): LKProof = proof match {
    case Axiom(s) => Axiom(s)
    case WeakeningLeftRule(p,s,o) if (forms.exists(x => x.isAncestor(o) && o.formula == x.formula)) => applyRec(p, forms)
    case WeakeningLeftRule(p,_,o) => WeakeningLeftRule(applyRec(p,forms), o.formula)
    case WeakeningRightRule(p,_,o) if (forms.exists(x => x.isAncestor(o) && o.formula == x.formula)) => applyRec(p, forms)
    case WeakeningRightRule(p,_,o) => WeakeningRightRule(applyRec(p,forms), o.formula)
    case ContractionLeftRule(p,_,a1,_,_) => ContractionLeftRule(applyRec(p,forms),a1.formula)
    case ContractionRightRule(p,_,a1,_,_) => ContractionRightRule(applyRec(p,forms),a1.formula)
    case CutRule(p1,p2,_,o1,_) => CutRule(applyRec(p1,forms),applyRec(p2,forms),o1.formula)
    case AndRightRule(p1,p2,_,o1,o2,_) => AndRightRule(applyRec(p1,forms),applyRec(p2,forms),o1.formula,o2.formula)
    case OrLeftRule(p1,p2,_,o1,o2,_) => OrLeftRule(applyRec(p1,forms),applyRec(p2,forms),o1.formula,o2.formula)
    case AndLeft1Rule(p,_,_,fo) => 
      val And(f1, f2) = fo.formula
      AndLeft1Rule(applyRec(p, forms), f1, f2)
    case AndLeft2Rule(p,_,_,fo) => 
      val And(f1, f2) = fo.formula
      AndLeft2Rule(applyRec(p, forms), f1, f2)
    case OrRight1Rule(p,_,_,fo) => 
      val Or(f1, f2) = fo.formula
      OrRight1Rule(applyRec(p, forms), f1, f2)
    case OrRight2Rule(p,_,_,fo) => 
      val Or(f1, f2) = fo.formula
      OrRight2Rule(applyRec(p, forms), f1, f2)
    case ImpLeftRule(p1,p2,_,o1,o2,_) => ImpLeftRule(applyRec(p1, forms),applyRec(p2, forms),o1.formula,o2.formula)
    case ImpRightRule(p1,_,o1,o2,_) => ImpRightRule(applyRec(p1, forms),o1.formula,o2.formula)
    case NegRightRule(p1,_,o1,_) => NegRightRule(applyRec(p1, forms),o1.formula)
    case NegLeftRule(p1,_,o1,_) => NegLeftRule(applyRec(p1, forms),o1.formula)
    case EquationLeft1Rule(p1,p2,_,o1,o2,o3) => EquationLeft1Rule(applyRec(p1, forms),applyRec(p2, forms),o1.formula,o2.formula,o3.formula)
    case EquationLeft2Rule(p1,p2,_,o1,o2,o3) => EquationLeft2Rule(applyRec(p1, forms),applyRec(p2, forms),o1.formula,o2.formula,o3.formula)
    case EquationRight1Rule(p1,p2,_,o1,o2,o3) => EquationRight1Rule(applyRec(p1, forms),applyRec(p2, forms),o1.formula,o2.formula,o3.formula)
    case EquationRight2Rule(p1,p2,_,o1,o2,o3) => EquationRight2Rule(applyRec(p1, forms),applyRec(p2, forms),o1.formula,o2.formula,o3.formula)
    case DefinitionLeftRule(p1,_,o1,o2) => DefinitionLeftRule(applyRec(p1, forms),o1.formula,o2.formula)
    case DefinitionRightRule(p1,_,o1,o2) => DefinitionRightRule(applyRec(p1, forms),o1.formula,o2.formula)
    case ForallLeftRule(p1,_,o1,o2,e) => ForallLeftRule(applyRec(p1, forms),o1.formula,o2.formula,e)
    case ForallRightRule(p1,_,o1,o2,e) => ForallRightRule(applyRec(p1, forms),o1.formula,o2.formula,e)
    case ExistsLeftRule(p1,_,o1,o2,e) => ExistsLeftRule(applyRec(p1, forms),o1.formula,o2.formula,e)
    case ExistsRightRule(p1,_,o1,o2,e) => ExistsRightRule(applyRec(p1, forms),o1.formula,o2.formula,e)
=======
  def apply(p: LKProof) : LKProof = {
    val (proof, ws) = cleanStructuralRules(p)
    // TODO: this assertion needs to change
    //assert(ws.forall(f => (p.root.antecedent ++ p.root.succedent).map(_.formula).contains(f)))
    addWeakenings(proof, p.root.toFSequent)
>>>>>>> .merge-right.r1940
  }

  // Note: using a pair instead of a sequent because sequents are composed of 
  // formula occurrences and not formulas.
  private def cleanStructuralRules(pr: LKProof) : (LKProof, (List[HOLFormula], List[HOLFormula])) = pr match {
    // Base case: axiom
    case Axiom(s) => ( pr, (Nil, Nil) )

    // Structural rules:
    
    case WeakeningLeftRule(p, _, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      ( proof, (ws._1 :+ m.formula, ws._2) )
    
    case WeakeningRightRule(p, _, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      ( proof, (ws._1, ws._2 :+ m.formula) )

    case ContractionLeftRule(p, _, a1, a2, m) =>
<<<<<<< .working
      // Assuming that above this contraction there are no more redundant
      // contractions (it is the top most)
      val new_proof = cleanStructuralRules(p)

      // Finding corresponding occurrences on the new proof (both should be there!!!)
      val new_a1 = new_proof.root.antecedent.filter(x => x.syntaxEquals(a1))(0)
      val new_a2 = new_proof.root.antecedent.filter(x => x.syntaxEquals(a2))(1)

      val w1 = isWeakened(new_a1, new_proof)
      val w2 = isWeakened(new_a2, new_proof)
      
      // Both formulas are weakened at some point
      if(w1 && w2) {
        // Only remove the weakening of one of those
        // NOTE: By returning this proof, the contraction rule is automatically
        // removed.
        removeWeakeningOn(new_a1, new_proof)
=======
      val (proof, ws) = cleanStructuralRules(p)
      ws._1.count(f => f == a1.formula) match {
        case n if n >= 2 => ( proof, (ws._1.diff(List(a1.formula, a2.formula)) :+ m.formula, ws._2) ) 
        case n if n == 1 => ( proof, (ws._1.diff(List(a1.formula)), ws._2) )
        case n if n == 0 => ( ContractionLeftRule(proof, a1.formula), ws )
>>>>>>> .merge-right.r1940
      }

    case ContractionRightRule(p, _, a1, a2, m) =>
<<<<<<< .working
      // Assuming that above this contraction there are no more redundant
      // contractions (it is the top most)
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrences on the new proof (both should be there!!!)
      val new_a1 = new_proof.root.succedent.filter(x => x.syntaxEquals(a1))(0)
      val new_a2 = new_proof.root.succedent.filter(x => x.syntaxEquals(a2))(1)

      val w1 = isWeakened(new_a1, new_proof)
      val w2 = isWeakened(new_a2, new_proof)
      
      // Both formulas are weakened at some point
      if(w1 && w2) {
        // Only remove the weakening of one of those
        // NOTE: By returning this proof, the contraction rule is automatically
        // removed.
        removeWeakeningOn(new_a1, new_proof)
=======
      val (proof, ws) = cleanStructuralRules(p)
      ws._2.count(f => f == a1.formula) match {
        case n if n >= 2 => ( proof, (ws._1, ws._2.diff(List(a1.formula, a2.formula)) :+ m.formula) ) 
        case n if n == 1 => ( proof, (ws._1, ws._2.diff(List(a1.formula))) )
        case n if n == 0 => ( ContractionRightRule(proof, a1.formula), ws )
>>>>>>> .merge-right.r1940
      }
 
    case CutRule(p1, p2, _, a1, a2) =>
<<<<<<< .working
      val new_proof1 = cleanStructuralRules(p1)
      val new_proof2 = cleanStructuralRules(p2)
      CutRule(new_proof1, new_proof2, a1.formula)

    // Logical rules:
    case OrLeftRule(p1, p2, _, a1, a2, m) =>
      val new_proof1 = cleanStructuralRules(p1)
      val new_proof2 = cleanStructuralRules(p2)

      // Finding corresponding occurrences on the new proofs
      val new_a1 = new_proof1.root.antecedent.filter(x => x.syntaxEquals(a1))(0)
      val new_a2 = new_proof2.root.antecedent.filter(x => x.syntaxEquals(a2))(0)

      val w1 = isWeakened(new_a1, new_proof1)
      val w2 = isWeakened(new_a2, new_proof2)

      if(w1) {
        val new_proof12 = removeWeakeningOn(new_a1, new_proof1)
        addWeakenings(new_proof12, proof.root.toFSequent)
=======
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      ( wsl._2.contains(a1.formula), wsr._1.contains(a2.formula) ) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula)) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( CutRule(p, proof2, a1.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( CutRule(proof1, p, a1.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( CutRule(proof1, proof2, a1.formula), (ws_1, ws_2) )
>>>>>>> .merge-right.r1940
      }
<<<<<<< .working
      else if(w2) {
        val new_proof22 = removeWeakeningOn(new_a2, new_proof2)
        addWeakenings(new_proof22, proof.root.toFSequent)
      }
      else OrLeftRule(new_proof1, new_proof2, a1.formula, a2.formula)
    
    case AndRightRule(p1, p2, _, a1, a2, m) =>
      val new_proof1 = cleanStructuralRules(p1)
      val new_proof2 = cleanStructuralRules(p2)
      
      // Finding corresponding occurrences on the new proofs
      val new_a1 = new_proof1.root.succedent.filter(x => x.syntaxEquals(a1))(0)
      val new_a2 = new_proof2.root.succedent.filter(x => x.syntaxEquals(a2))(0)
=======
>>>>>>> .merge-right.r1940

    // Unary rules, one aux formula:

    case NegLeftRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p) 
      ws._2.contains(a.formula) match {
        case true => ( proof, (ws._1 :+ m.formula, ws._2.diff(List(a.formula))) )
        case false => ( NegLeftRule(proof, a.formula), ws )
      }
  
    case NegRightRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p) 
      ws._1.contains(a.formula) match {
        case true => ( proof, (ws._1.diff(List(a.formula)), ws._2 :+ m.formula) )
        case false => ( NegRightRule(proof, a.formula), ws )
      }
<<<<<<< .working
      else AndRightRule(new_proof1, new_proof2, a1.formula, a2.formula)
    
    case NegLeftRule(p, _, a, m) =>
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.succedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningLeftRule(new_proof2, m.formula)
      }
      else NegLeftRule(new_proof, a.formula)
    
=======
 
>>>>>>> .merge-right.r1940
    case AndLeft1Rule(p, _, a, m) =>
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      val a2 = m.formula match {case And(_,r) => r}

      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.antecedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningLeftRule(new_proof2, m.formula)
      }
      else AndLeft1Rule(new_proof, a.formula, a2)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case And(_, r) => r}; AndLeft1Rule(p, a, a2) } )
>>>>>>> .merge-right.r1940
    
    case AndLeft2Rule(p, _, a, m) =>
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      val a2 = m.formula match {case And(l,_) => l}
     
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.antecedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningLeftRule(new_proof2, m.formula)
      }
      else AndLeft2Rule(new_proof, a2, a.formula)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case And(l, _) => l}; AndLeft2Rule(p, a2, a) } )
>>>>>>> .merge-right.r1940
    
    case OrRight1Rule(p, _, a, m) =>
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      val a2 = m.formula match {case Or(_,r) => r}
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.succedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningRightRule(new_proof2, m.formula)
      }
      else OrRight1Rule(new_proof, a.formula, a2)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case Or(_, r) => r}; OrRight1Rule(p, a, a2) } )
>>>>>>> .merge-right.r1940
    
    case OrRight2Rule(p, _, a, m) =>
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      val a2 = m.formula match {case Or(l,_) => l}
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.succedent.filter(x => x.syntaxEquals(a))(0)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case Or(l, _) => l}; OrRight2Rule(p, a2, a) } )
 
    case ForallLeftRule(p, _, a, m, t) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => ForallLeftRule(p, a, m, t) } )
>>>>>>> .merge-right.r1940

<<<<<<< .working
      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningRightRule(new_proof2, m.formula)
      }
      else OrRight2Rule(new_proof, a2, a.formula)
    
    case NegRightRule(p, _, a, m) =>
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.antecedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningRightRule(new_proof2, m.formula)
      }
      else NegRightRule(new_proof, a.formula)
    
    case ImpLeftRule(p1, p2, _, a1, a2, m) =>
      val new_proof1 = cleanStructuralRules(p1)
      val new_proof2 = cleanStructuralRules(p2)
      
      // Finding corresponding occurrences on the new proofs
      val new_a1 = new_proof1.root.succedent.filter(x => x.syntaxEquals(a1))(0)
      val new_a2 = new_proof2.root.antecedent.filter(x => x.syntaxEquals(a2))(0)

      val w1 = isWeakened(new_a1, new_proof1)
      val w2 = isWeakened(new_a2, new_proof2)

      if(w1) {
        val new_proof12 = removeWeakeningOn(new_a1, new_proof1)
        addWeakenings(new_proof12, proof.root.toFSequent)
      }
      else if(w2) {
        val new_proof22 = removeWeakeningOn(new_a2, new_proof2)
        addWeakenings(new_proof22, proof.root.toFSequent)
      }
      else ImpLeftRule(new_proof1, new_proof2, a1.formula, a2.formula)
    
    case ImpRightRule(p, _, a1, a2, m) =>
      val new_proof = cleanStructuralRules(p)
      ImpRightRule(new_proof, a1.formula, a2.formula)

    case ForallLeftRule(p, _, a, m, t) => 
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.antecedent.filter(x => x.syntaxEquals(a))(0)

      val w1 = isWeakened(new_a, new_proof)
      
      if(w1) {
        val new_proof2 = removeWeakeningOn(new_a, new_proof)
        WeakeningLeftRule(new_proof2, m.formula)
      }
      else ForallLeftRule(new_proof, a.formula, m.formula, t)

=======
>>>>>>> .merge-right.r1940
    case ForallRightRule(p, _, a, m, t) => 
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.succedent.filter(x => x.syntaxEquals(a))(0)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => ForallRightRule(p, a, m, t) } )
>>>>>>> .merge-right.r1940

    case ExistsLeftRule(p, _, a, m, t) => 
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.antecedent.filter(x => x.syntaxEquals(a))(0)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => ExistsLeftRule(p, a, m, t) } )
>>>>>>> .merge-right.r1940

    case ExistsRightRule(p, _, a, m, t) => 
<<<<<<< .working
      val new_proof = cleanStructuralRules(p)
      
      // Finding corresponding occurrence on the new proof
      val new_a = new_proof.root.succedent.filter(x => x.syntaxEquals(a))(0)
=======
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => ExistsRightRule(p, a, m, t) } )
>>>>>>> .merge-right.r1940

    // Schema rules (all unary with one aux formula):
    case AndLeftEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => AndLeftEquivalenceRule1(p, a, m) } )

    case AndRightEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => AndRightEquivalenceRule1(p, a, m) } )
    
    case OrLeftEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => OrLeftEquivalenceRule1(p, a, m) } )
    
    case OrRightEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => OrRightEquivalenceRule1(p, a, m) } )
    
    case AndLeftEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => AndLeftEquivalenceRule3(p, a, m) } )
    
    case AndRightEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => AndRightEquivalenceRule3(p, a, m) } )
    
    case OrLeftEquivalenceRule3(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => OrLeftEquivalenceRule3(p, a, m) } )
    
    case OrRightEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => OrRightEquivalenceRule3(p, a, m) } )

    // Definition rules (all unary with one aux formula):
    case DefinitionLeftRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => DefinitionLeftRule(p, a, m) } )

    case DefinitionRightRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => DefinitionRightRule(p, a, m) } )

    // Unary rules, two aux formulas:

    case ImpRightRule(p, _, a1, a2, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      (ws._1.contains(a1.formula), ws._2.contains(a2.formula)) match {
        case (true, true) => 
          val ws_1 = ws._1.diff(List(a1.formula))
          val ws_2 = ws._2.diff(List(a2.formula)) :+ m.formula
          ( proof, (ws_1, ws_2) ) 
        case (true, false) => 
          val p1 = WeakeningLeftRule(proof, a1.formula)
          val p2 = ImpRightRule(p1, a1.formula, a2.formula)
          ( p2, (ws._1.diff(List(a1.formula)), ws._2) )
        case (false, true) => 
          val p1 = WeakeningRightRule(proof, a2.formula)
          val p2 = ImpRightRule(p1, a1.formula, a2.formula)
          ( p2, (ws._1, ws._2.diff(List(a2.formula))) )
        case (false, false) => ( ImpRightRule(proof, a1.formula, a2.formula), ws )
      }

<<<<<<< .working
    // Structural rules:
    case WeakeningLeftRule(p, _, m) =>
      if(getAncestors(f).contains(m) && f.syntaxEquals(m)) true
      else isWeakened(f, p) 
    case WeakeningRightRule(p, _, m) =>
      if(getAncestors(f).contains(m) && f.syntaxEquals(m)) true
      else isWeakened(f, p) 
    case ContractionLeftRule(p, _, _, _, _) => isWeakened(f, p)
    case ContractionRightRule(p, _, _, _, _) => isWeakened(f, p)
    case CutRule(p1, p2, _, _, _) => isWeakened(f, p1) || isWeakened(f, p2)
=======
    // Binary rules:
>>>>>>> .merge-right.r1940

    case OrLeftRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._1.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = (( wsl._1.diff(List(a1.formula)) ++ wsr._1.diff(List(a2.formula)) ) :+ m.formula) ++ ant2
          val ws_2 = wsl._2 ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1.diff(List(a1.formula)) ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof1, a1.formula)
          ( OrLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( OrLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( OrLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
      }

<<<<<<< .working
    // Schema rules:
    case AndLeftEquivalenceRule1(p, _, a, m) => isWeakened(f, p)
    case AndRightEquivalenceRule1(p, _, a, m) => isWeakened(f, p) 
    case OrLeftEquivalenceRule1(p, _, a, m) => isWeakened(f, p)
    case OrRightEquivalenceRule1(p, _, a, m) => isWeakened(f, p)
    case AndLeftEquivalenceRule3(p, _, a, m) => isWeakened(f, p)
    case AndRightEquivalenceRule3(p, _, a, m) => isWeakened(f, p)
    case OrLeftEquivalenceRule3(p, _, a, m) => isWeakened(f, p)
    case OrRightEquivalenceRule3(p, _, a, m) => isWeakened(f, p)
    
    case _ => throw new Exception("ERROR: Unexpected rule while checking if a formula is weakened in a proof.")
  }

  // Removes the weakening on some ancestor of f (such that it is not a proper
  // subformula of f)
  private def removeWeakeningOn(f: FormulaOccurrence, proof: LKProof) : LKProof = proof match {
     case Axiom(s) => proof

    // Structural rules:
    case WeakeningLeftRule(p, _, m) => 
      if(getAncestors(f).contains(m) && f.syntaxEquals(m)) p
      else {
        val new_proof = removeWeakeningOn(f, p) 
        WeakeningLeftRule(new_proof, m.formula)
=======
    case AndRightRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( AndRightRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( AndRightRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( AndRightRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
>>>>>>> .merge-right.r1940
      }
<<<<<<< .working
    case WeakeningRightRule(p, _, m) =>
      if(getAncestors(f).contains(m) && f.syntaxEquals(m)) p
      else {
        val new_proof = removeWeakeningOn(f, p) 
        WeakeningRightRule(new_proof, m.formula)
=======
      
    case ImpLeftRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( ImpLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( ImpLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( ImpLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
>>>>>>> .merge-right.r1940
      }
   
    // Equation rules (all binary):
    case EquationLeft1Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationLeft1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( EquationLeft1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationLeft1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationLeft2Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationLeft2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( EquationLeft2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationLeft2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationRight1Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationRight1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( EquationRight1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationRight1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationRight2Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationRight2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( EquationRight2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationRight2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

<<<<<<< .working
    case AndLeft1Rule(p, _, a, m) =>
      val new_proof = removeWeakeningOn(f, p)
      val a2 = m.formula match {case And(_,r) => r}
      AndLeft1Rule(new_proof, a.formula, a2)

    case AndLeft2Rule(p, _, a, m) =>
      val new_proof = removeWeakeningOn(f, p)
      val a2 = m.formula match {case And(l,_) => l}
      AndLeft2Rule(new_proof, a2, a.formula)

    case AndRightRule(p1, p2, _, a1, a2, m) => 
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      AndRightRule(new_proof1, new_proof2, a1.formula, a2.formula)

    case OrRight1Rule(p, _, a, m) =>
      val new_proof = removeWeakeningOn(f, p)
      val a2 = m.formula match {case Or(_,r) => r}
      OrRight1Rule(new_proof, a.formula, a2)

    case OrRight2Rule(p, _, a, m) =>
      val new_proof = removeWeakeningOn(f, p)
      val a2 = m.formula match {case Or(l,_) => l}
      OrRight2Rule(new_proof, a2, a.formula)

    case OrLeftRule(p1, p2, _, a1, a2, m) => 
      val new_proof1 = removeWeakeningOn(f, p1) 
      val new_proof2 = removeWeakeningOn(f, p2)
      OrLeftRule(new_proof1, new_proof2, a1.formula, a2.formula)

    case ImpLeftRule(p1, p2, _, a1, a2, m) => 
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      ImpLeftRule(new_proof1, new_proof2, a1.formula, a2.formula)

    case ImpRightRule(p, _, a1, a2, m) =>
      val new_proof = removeWeakeningOn(f, p)
      ImpRightRule(new_proof, a1.formula, a2.formula)

    case ForallLeftRule(p, _, a, m, t) => 
      val new_proof = removeWeakeningOn(f, p)
      ForallLeftRule(new_proof, a.formula, m.formula, t)

    case ForallRightRule(p, _, a, m, t) => 
      val new_proof = removeWeakeningOn(f, p)
      ForallRightRule(new_proof, a.formula, m.formula, t)

    case ExistsLeftRule(p, _, a, m, t) => 
      val new_proof = removeWeakeningOn(f, p)
      ExistsLeftRule(new_proof, a.formula, m.formula, t)

    case ExistsRightRule(p, _, a, m, t) => 
      val new_proof = removeWeakeningOn(f, p)
      ExistsRightRule(new_proof, a.formula, m.formula, t)

    case EquationLeft1Rule(p1,p2,_,o1,o2,o3) =>
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      EquationLeft1Rule(new_proof1,new_proof2,o1.formula,o2.formula,o3.formula)

    case EquationLeft2Rule(p1,p2,_,o1,o2,o3) =>
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      EquationLeft2Rule(new_proof1,new_proof2,o1.formula,o2.formula,o3.formula)

    case EquationRight1Rule(p1,p2,_,o1,o2,o3) =>
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      EquationRight1Rule(new_proof1,new_proof2,o1.formula,o2.formula,o3.formula)

    case EquationRight2Rule(p1,p2,_,o1,o2,o3) =>
      val new_proof1 = removeWeakeningOn(f, p1)
      val new_proof2 = removeWeakeningOn(f, p2)
      EquationRight2Rule(new_proof1,new_proof2,o1.formula,o2.formula,o3.formula)

    case DefinitionLeftRule(p1,_,o1,o2) =>
      val new_proof = removeWeakeningOn(f, p1)
      DefinitionLeftRule(new_proof,o1.formula,o2.formula)

    case DefinitionRightRule(p1,_,o1,o2) =>
      val new_proof = removeWeakeningOn(f, p1)
      DefinitionRightRule(new_proof,o1.formula,o2.formula)


     // Schema rules:
    case AndLeftEquivalenceRule1(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      AndLeftEquivalenceRule1(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

    case AndRightEquivalenceRule1(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      AndRightEquivalenceRule1(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case OrLeftEquivalenceRule1(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      OrLeftEquivalenceRule1(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case OrRightEquivalenceRule1(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      OrRightEquivalenceRule1(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case AndLeftEquivalenceRule3(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      AndLeftEquivalenceRule3(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case AndRightEquivalenceRule3(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      AndRightEquivalenceRule3(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case OrLeftEquivalenceRule3(p, _, a, m) =>
      val new_proof = removeWeakeningOn(f, p)
      OrLeftEquivalenceRule3(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    
    case OrRightEquivalenceRule3(p, _, a, m) => 
      val new_proof = removeWeakeningOn(f, p)
      OrRightEquivalenceRule3(new_proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

    case _ => throw new Exception("ERROR: Unexpected rule while removing weakening of a formula.")
=======
    case _ => throw new Exception("ERROR: Unexpected case while cleaning redundant structural rules.")
>>>>>>> .merge-right.r1940
  }
  
  
  private def handle_unary_one_aux_left (proof: LKProof, 
                                    ws: (List[HOLFormula], List[HOLFormula]), 
                                    aux: HOLFormula, 
                                    m: HOLFormula,
                                    rule: ((LKProof, HOLFormula, HOLFormula) => LKProof) ) 
  : (LKProof, (List[HOLFormula], List[HOLFormula])) = 
    ws._1.contains(aux) match {
      case true => ( proof, (ws._1.diff(List(aux)) :+ m, ws._2) )
      case false => (rule(proof, aux, m), ws)
    }

  private def handle_unary_one_aux_right (proof: LKProof, 
                                    ws: (List[HOLFormula], List[HOLFormula]), 
                                    aux: HOLFormula, 
                                    m: HOLFormula,
                                    rule: ((LKProof, HOLFormula, HOLFormula) => LKProof) ) 
  : (LKProof, (List[HOLFormula], List[HOLFormula])) = 
    ws._2.contains(aux) match {
      case true => ( proof, (ws._1, ws._2.diff(List(aux)) :+ m) )
      case false => (rule(proof, aux, m), ws)
    }
}
