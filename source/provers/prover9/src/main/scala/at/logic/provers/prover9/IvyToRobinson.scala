package at.logic.provers.prover9.ivy.conversion
import at.logic.provers.prover9.ivy.{InitialClause => IInitialClause, Instantiate => IInstantiate, Resolution => IResolution,
                                 Paramodulation => IParamodulation, IvyResolutionProof, Flip, Propositional => IPropositional}
import at.logic.calculi.resolution.robinson.{InitialClause => RInitialClause, Resolution => RResolution, Factor => RFactor,
  Variant => RVariant, Paramodulation => RParamodulation, RobinsonResolutionProof}
import at.logic.language.fol.{FOLExpression, FOLTerm, FOLFormula}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, VariantGenerator, Var}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.instance.{Instance => RInstantiate}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.base.Clause
import at.logic.language.fol
import collection.immutable
import at.logic.language.lambda.symbols.VariableStringSymbol

/**
 * Converts Ivy Proofs into Robinson Resolution Proofs
 */
object IvyToRobinson {
  val generator : VariantGenerator = new VariantGenerator( new {var c = 10000; def nextId = {c = c+1; c}} , "iv" )
  type ProofMap = immutable.Map[String, RobinsonResolutionProof]

  def apply(iproof : IvyResolutionProof) : RobinsonResolutionProof = apply(iproof, immutable.Map[String, RobinsonResolutionProof]())._1
  def apply(iproof : IvyResolutionProof, map :  ProofMap) : (RobinsonResolutionProof, ProofMap) = iproof match {
    case IInitialClause(id, exp, clause) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val rproof = RInitialClause(clause.negative map (_.formula.asInstanceOf[FOLFormula]), clause.positive map (_.formula.asInstanceOf[FOLFormula]))
          require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating initial rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
          (rproof, map + ((id,rproof)))
      }

    case IInstantiate(id, exp, sub, clause, parent) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val (pproof, parentmap) = IvyToRobinson(parent, map)
          val rproof = RInstantiate(pproof, sub.asInstanceOf[Substitution[FOLExpression]])
          require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating instantiation rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
          (rproof, parentmap + ((id, rproof)))
      }
    case IResolution(id, exp, lit1, lit2, clause, parent1, parent2) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          //try {
          val (rparent1, parentmap1) = IvyToRobinson(parent1, map)
          val (rparent2, parentmap2) = IvyToRobinson(parent2, parentmap1)
          println("conclusion:"+clause)
          println("resolving over 1:"+parent1.root+"/"+rparent1.root)
          println("resolving over 2:"+parent2.root+"/"+rparent2.root)
          val (polarity1, _, index1) = getIndex(lit1, parent1.vertex, rparent1.vertex)
          val (polarity2, _, index2) = getIndex(lit2, parent2.vertex, rparent2.vertex)

          (polarity1, polarity2) match {
            case (true,false) =>
              require(rparent1.vertex.succedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
              require(rparent2.vertex.antecedent(index2).formula == lit2.formula,
                "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

              val rproof = RResolution(rparent1, rparent2, rparent1.vertex.succedent(index1), rparent2.vertex.antecedent(index2), Substitution[FOLExpression]())
              require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating resolution rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
              (rproof, parentmap2 + ((id, rproof)))
            case (false,true) =>
              require(rparent1.vertex.antecedent(index1).formula == lit1.formula, "Left parent literal must be correctly found!")
              require(rparent2.vertex.succedent(index2).formula == lit2.formula,
                "Right parent literal "+lit2+" at pos "+ index2 +" must be correctly found!" + rparent2.vertex)

              val rproof = RResolution(rparent2, rparent1, rparent2.vertex.succedent(index2), rparent1.vertex.antecedent(index1), Substitution[FOLExpression]())
              require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating resolution rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
              (rproof, parentmap2 + ((id, rproof)))
            case _ => throw new Exception("Error in processing ivy proof: resolved literals "+lit1+" and "+lit2+
                                          " do not have different polarity!")
          }
          //} catch {
          //  case e:Exception =>
          //    if ("""exception""".r.findPrefixMatchOf(e.getMessage).isEmpty  )
          //      throw new Exception("exception with inference "+id+" from "+parent1.id+" and "+parent2.id,e)
          //    else throw e
          //}
      }

    case IPropositional(id, exp, clause, parent) =>
      def remove_first(el:FormulaOccurrence, l:immutable.Seq[FormulaOccurrence])
         : (FormulaOccurrence, immutable.List[FormulaOccurrence]) = l.toList match {
        case x::Nil =>
          if (x.formula == el.formula)
            (x, Nil)
          else {
            throw new Exception("Error: element "+el+" to remove not contained in list!")
          }
        case x::xs =>
          if (x.formula == el.formula)
            (x, xs)
          else {
            val (removed, rest) = remove_first(el,xs)
            (removed, x::rest)
          }
        case Nil => throw new Exception("Error: want to remove element "+el+" from an empty list!")
      }

      def remove_firsts(fs:immutable.Seq[FormulaOccurrence], l:immutable.Seq[FormulaOccurrence]) :
       (immutable.List[FormulaOccurrence], immutable.Seq[FormulaOccurrence]) = {
        if (fs.isEmpty) { (Nil, l) } else {
            val (el, rest) = remove_first(fs.head,l)
            val (r1,r2) = remove_firsts(fs.tail, rest)
            (el::r1, r2)
        }
      }

      def connect(ivy : immutable.List[FormulaOccurrence], robinson : immutable.Seq[FormulaOccurrence])
           : immutable.List[FormulaOccurrence] = ivy match {
        case x::xs =>
          val (rancs, rem) = remove_firsts(x.ancestors.toList, robinson)
          new FormulaOccurrence(x.formula, rancs, x.factory) :: connect(xs, rem)

        case Nil => Nil
      }

      def find_matching(what:immutable.List[FormulaOccurrence], where : immutable.List[FormulaOccurrence])
            : immutable.List[FormulaOccurrence]= what match {
        case x::xs =>
          val (y, rest) = remove_first(x,where)
          y :: find_matching(xs, rest)
        case Nil => Nil
      }

      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>

          val (rparent, parentmap) = IvyToRobinson(parent, map)
          val contracted  = (clause.antecedent ++ clause.succedent) filter (_.ancestors.size >1)
          require(contracted.size == 1, "Error: only one aux formula may have been factored!")
          val ianc = contracted(0).ancestors
          val aux::deleted = find_matching(ianc.toList, (rparent.vertex.antecedent ++ rparent.vertex.succedent).toList)
          val rproof = RFactor(rparent, aux, deleted, Substitution[FOLExpression]())
          require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating propoistional rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
          (rproof, parentmap + ((id, rproof)))
      }

    case Flip(id, exp, flipped, clause, parent) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val (rparent, parentmap) = IvyToRobinson(parent, map)

          //there is no robinson rule for flip, so we simulate it: from P :- Q, s=t and :- s=s prove P :- Q, t=s by paramod
          val fol.Equation(s,t) = flipped.formula

          //create a proof of s=s
          val x = fol.FOLVar(new VariableStringSymbol("x"))
          val xx = RInitialClause(Nil, fol.Equation(x,x)::Nil)
          val ss = RInstantiate(xx, Substitution[FOLExpression]((x,t)))
          println("instantiate "+ss)
          //val ts = fol.Equation(s,t)


          //println("translating inference "+id)
          //require((rparent.root.antecedent ++ rparent.root.succedent) contains (flipped.ancestors(0)),
          //  "Error translating flip rule: "+flipped+" anc: "+flipped.ancestors(0) + " not contained in "+ ((rparent.root.antecedent ++ rparent.root.succedent) map (_.id)) )

          val flippend_ancestor = flipped.ancestors(0).formula
          val rflipped = (rparent.root.negative ++ rparent.root.positive) find (_.formula == flippend_ancestor)
          require(rflipped.nonEmpty, "Error: cannot find flipped formula in translation of parent proof!")

          println("flipping: "+flipped.ancestors(0)+" transformed flipped "+rflipped.get)

          val rproof = RParamodulation(ss, rparent, ss.root.positive(0), rflipped.get, flipped.formula.asInstanceOf[FOLFormula], Substitution[FOLExpression]())
          println("from: "+flipped.ancestors(0)+" tfrom to "+rflipped.get )
          println("flipped formula: "+flipped.formula)
          require((rproof.root.antecedent ++ rproof.root.succedent).map(_.formula).contains(flipped.formula), "flipped formula must occur in translated clause "+rproof.root)
          require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating flip rule, expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
          (rproof, parentmap + ((id, rproof)))
      }

    case IParamodulation(id, exp, pos, lit, clause, parent1, parent2) =>
      map.get(id) match {
        case Some(proof) => (proof, map)
        case None =>
          val (rparent1, parentmap1) = IvyToRobinson(parent1, map)
          val (rparent2, parentmap2) = IvyToRobinson(parent2, parentmap1)
          println("translating inference "+id+ " from "+parent1.id+" and "+parent2.id)
          require(lit.ancestors.length == 2, "Error in converting a paramodulation inference: need two ancestors")
          if (rparent1 == rparent2) {
            //TODO:wrong auxiliary formulas
            val rproof = RParamodulation(rparent1, rparent2, lit.ancestors(0), lit.ancestors(1), lit.formula.asInstanceOf[FOLFormula], Substitution[FOLExpression]() )
            (rproof, parentmap2 + ((id, rproof)))
          } else {
            require(parent1.id != parent2.id, "Parents need to be different!")
            val p1lits = (rparent1.root.negative ++ rparent1.root.positive)
            val p2lits = (rparent2.root.negative ++ rparent2.root.positive)
            val p1litsf = (rparent1.root.negative ++ rparent1.root.positive) map (_.formula)
            val p2litsf = (rparent2.root.negative ++ rparent2.root.positive) map (_.formula)
            println(lit.ancestors)
            println(parent1.root.antecedent + " :- "+parent1.root.succedent)
            println(rparent1.root.antecedent + " :- "+rparent1.root.succedent)
            println(rparent2.root.antecedent + " :- "+rparent2.root.succedent)
            val anc1 = lit.ancestors filter (p1litsf contains _.formula)
            val anc2 = lit.ancestors filter (p2litsf contains _.formula)
            require(anc1.length + anc2.length >= 2, "Error in converting a paramodulation inference: sum of ancestors in parents needs to be 2 not"+anc1.length + " "+anc2.length)
            require(anc1.length >= 1, "Error in converting a paramodulation inference: need exactly one ancestor in first parent!")
            require(anc2.length >= 1, "Error in converting a paramodulation inference: need exactly one ancestor in second parent!")
            val anc1occ = p1lits( p1litsf.indexOf(anc1(0).formula) )
            val anc2occ = p2lits( p2litsf.indexOf(anc2(0).formula) )
            val rproof = RParamodulation(rparent1, rparent2, anc1occ, anc2occ, lit.formula.asInstanceOf[FOLFormula], Substitution[FOLExpression]() )

            println("root     :" +iproof.root)
            println("troot    :" +rproof.root)
            println("parent  1: "+parent1.root)
            println("tparent 1: "+rparent1.root)
            println("parent  2: "+parent2.root)
            println("tparent 2: "+rparent2.root)
            println("lit ancestors: "+lit.ancestors)
            println("a1: "+anc1occ)
            println("a2: "+anc2occ)


            require(rproof.root.toFSequent multiSetEquals clause.toFSequent, "Error translating para rule "+ id + ", expected: "+clause.toFSequent+" result:"+rproof.root.toFSequent)
            (rproof, parentmap2 + ((id, rproof)))
          }
      }






        /*
            case IResolution(id, exp, lit1, lit2, clause, parent1, parent2) =>
              (parent1,parent2) match {
                case (IInstantiate(id1,exp1,sub1, clause1, parent1), IInstantiate(id2,exp2,sub2, clause2, parent2) ) =>
                  val shared_vars : Set[Var] = sub1.map.keySet.intersect(sub2.map.keySet)

                  val new_vars : Map[Var,FOLTerm]=
                    Map[Var,FOLTerm]() ++ (shared_vars map ((x:Var) => (x,x.variant(generator).asInstanceOf[FOLTerm])))

                  val sub2_ = for ((key,value) <-  sub2.map) yield {
                    if (shared_vars contains key)
                      (new_vars(key), value)
                    else
                      (key,value)
                  }

                  val variant_sub = Substitution[FOLTerm](new_vars.toList)

                  apply(iproof)

              }

        */
  }

  /* params: fo ... occurrence in c, d ... clause to search
   * returns: triple:
   *   _1 positive or negative literal
   *   _2 position of fo in c
   *   _3 position of occurence with fo.formula in d */
  def getIndex(fo : FormulaOccurrence, c : Clause, d : Clause) : (Boolean, Int, Int) = {
    val index = c.antecedent.indexOf(fo)
    if (index < 0) {
      val index_ = c.succedent.indexOf(fo)
      if (index_ <0) throw new Exception("Error finding index of occurrence "+fo+ " in clause "+c)
      val dindex = d.succedent.indexWhere( _.formula == fo.formula )
      if (dindex <0) throw new Exception("Error finding occurrence of formula "+fo.formula+ " in clause "+d)
      (true, index_, dindex )
    }
    else {
      val dindex = d.antecedent.indexWhere( _.formula == fo.formula )
      if (dindex <0) throw new Exception("Error finding occurrence of formula "+fo.formula+ " in clause "+d)
      (false, index, dindex )
    }
  }

}