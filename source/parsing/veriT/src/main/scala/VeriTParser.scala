package at.logic.parsing.veriT

import scala.util.parsing.combinator._
import at.logic.language.fol._
import at.logic.language.fol.BetaReduction._
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, qFreeToExpansionTree}
import at.logic.algorithms.expansionTrees.prenexToExpansionTree._
import java.io.FileReader

object VeriTParser extends RegexParsers {

  type Instances = (FOLFormula, List[FOLFormula])

  // Fixes the order of the equalities for congruence predicates.
  // E.g.:
  // x1 = y1 ^ y2 = x2 -> f(x1, x2) = f(y1, y2)  should become
  // x1 = y1 ^ x2 = y2 -> f(x1, x2) = f(y1, y2)
  def fixOrder(pairs: List[(FOLTerm, FOLTerm)], eqs: List[FOLFormula]) : (List[FOLFormula], List[Instances]) = (pairs, eqs.head) match {
    case ( (x, y)::tail, Neg(Atom(eq, List(a, b))) ) if x==a && y==b =>
      val p = fixOrder(tail, eqs.tail)
      ((eqs.head :: p._1), p._2)
    case ( (x, y)::tail, Neg(Atom(eq, List(a, b))) ) if x==b && y==a =>
      val s = getSymmInstances(a, b)
      val p = fixOrder(tail, eqs.tail)
      ((Neg(Atom(eq, List(b, a))) :: p._1), s :: p._2)
    case ( (x, y)::tail, Neg(Atom(eq, List(a, b))) ) =>
      throw new Exception("ERROR: Predicate of function " + eqs.head + " does not have args " + x + ", " + y)
    case ( Nil, Atom(_,_) ) => (eqs, Nil)
    case ( Nil, Neg(Atom(_,_)) ) => (eqs, Nil)
    case _ => throw new Exception("ERROR: mal-formed eq_congruent or eq_congruent_pred.")

  }

  def getSymmInstances(a: FOLTerm, b: FOLTerm) : Instances = {
    val x = FOLVar("x")
    val y = FOLVar("y")
    val eq = "="
    val eq1 = Atom(eq, List(x, y))
    val eq2 = Atom(eq, List(y, x))
    val imp = Imp(eq1, eq2)
    val eq_symm = AllVar(x, AllVar(y, imp))

    val i1 = instantiate(instantiate(eq_symm, a), b)
    val i2 = instantiate(instantiate(eq_symm, b), a)

    (eq_symm, List(i1, i2))
  }
  
  def getEqReflInstances(f: List[FOLFormula]) : List[Instances] = {
    val x = FOLVar("x")
    val eq = "="
    val eq_refl = AllVar(x, Atom(eq, List(x, x)))
    List((eq_refl, f))
  }

  // Assuming all the antecedents of the implication are in order:
  // ( =(x0, x1)  ^  =(x1, x2)  ^ ... ^  =(xn-1, xn)  ->  =(x0, xn) )
  // in veriT is *always* ( not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) )
  def getEqTransInstances(l: List[FOLFormula]) : List[Instances] = {
    val x = FOLVar("x")
    val y = FOLVar("y")
    val z = FOLVar("z")
    val eq = "="
    val eq1 = Atom(eq, List(x, y))
    val eq2 = Atom(eq, List(y, z))
    val eq3 = Atom(eq, List(x, z))
    val imp = Imp(And(eq1, eq2), eq3)
    val eq_trans = AllVar(x, AllVar(y, AllVar(z, imp)))

    var symm = List[Instances]()

    // Transforms a transitivity chain (represented as a list):
    //
    // [ not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) ]
    //
    // into simple transitivity formulas:
    //
    // =(x0, x1) ^ =(x1, x2) -> =(x0, x2)
    // =(x0, x2) ^ =(x2, x3) -> =(x0, x3)
    // ...
    // =(x0, xn-1) ^ =(xn-1, xn) -> =(x0, xn)
    //
    def unfoldChain(l: List[FOLFormula]) = unfoldChain_(l.tail, l(0))
    def unfoldChain_(l: List[FOLFormula], c: FOLFormula) : List[FOLFormula] = l.head match {
      case Neg(Atom(eq0, List(x0, x1))) if eq0 == eq => c match {
        // Note that the variables are:
        // x2=x3 ^ x0=x1
        // Checking all possible cases of atom ordering:
 
        // x=y ^ y=z -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x3 == x0 =>
          val newc = Neg(Atom(eq, List(x2, x1)))
          // Instances
          val f1 = instantiate(eq_trans, x2)
          val f2 = instantiate(f1, x0) // or x3, should be the same
          val f3 = instantiate(f2, x1)

          f3 :: unfoldChain_(l.tail, newc)

        // x=y ^ z=y -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x3 == x1 =>
          val newc = Neg(Atom(eq, List(x2, x0)))
          // Instances
          val f1 = instantiate(eq_trans, x2)
          val f2 = instantiate(f1, x1) // or x3, should be the same
          val f3 = instantiate(f2, x0)

          symm = getSymmInstances(x0, x1) :: symm

          f3 :: unfoldChain_(l.tail, newc)

        // y=x ^ z=y -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x2 == x1 =>
          val newc = Neg(Atom(eq, List(x3, x0)))
          // Instances
          val f1 = instantiate(eq_trans, x3)
          val f2 = instantiate(f1, x1) // or x2, should be the same
          val f3 = instantiate(f2, x0)

          symm = getSymmInstances(x0, x1) :: symm
          symm = getSymmInstances(x2, x3) :: symm
          
          f3 :: unfoldChain_(l.tail, newc)
        
        // y=x ^ y=z -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x2 == x0 =>
          val newc = Neg(Atom(eq, List(x3, x1)))
          // Instances
          val f1 = instantiate(eq_trans, x3)
          val f2 = instantiate(f1, x0) // or x2, should be the same
          val f3 = instantiate(f2, x1)
          
          symm = getSymmInstances(x2, x3) :: symm

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) => throw new Exception("ERROR: the conclusion of the previous terms have" +  
          " no literal in common with the next one. Are the literals out of order?" + 
          "\nconclusion: " + c + "\nsecond literal: " + l.head)


        case _ => throw new Exception("ERROR: wrong format for negated equality: " + c)
      }

      case Neg(Atom(eq0, List(x0, x1))) if eq0 != eq => throw new Exception("ERROR: Predicate " + eq0 + 
        " in eq_transitive is not equality.")
      
      // When reaching the final literal, check if they are the same.
      case Atom(eq0, List(x0, x1)) if eq0 == eq => c match {
        case Neg(Atom(eq1, List(x2, x3))) if x0 == x2 && x1 == x3 => Nil
        case Neg(Atom(eq1, List(x2, x3))) if x1 == x2 && x0 == x3 => Nil
        
        case Neg(Atom(eq1, List(x2, x3))) => throw new Exception("ERROR: the conclusion of the previous terms" + 
          " have no literal in common with the conclusion of the chain. Are the literals out of order? Is the conclusion" + 
          " not the last one?")

        case _ => throw new Exception("ERROR: wrong format for negated equality: " + c)
      }

      case Atom(eq0, List(x0, x1)) if eq0 != eq => throw new Exception("ERROR: Predicate " + eq0 + 
        " in eq_transitive is not equality.")
    }

    val instances = unfoldChain(l)
    (eq_trans, instances) :: symm
  }

  // Assuming all the antecedents of the implication are in order:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn)  ->  =(f x0...xn, f y0...yn) )
  // in veriT is *always* ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), =(f x0...xn, f y0...yn) )
  def getEqCongrInstances(f: List[FOLFormula]) : List[Instances] = {

    def getFunctionName(f: FOLFormula) = f match {
      case Atom(eq, List(f1, _)) => f1 match {
        case Function(n, _) => n.toString 
      }
    }
    
    def getArgsLst(f: FOLFormula) = f match {
      case Atom(eq, List(f1, f2)) => (f1, f2) match {
        case (Function(_, args1), Function(_, args2)) => (args1, args2) 
      }
    }

    // Generate the eq_congruent formula with the right number of literals
    def gen_eq_congr(n: Int, fname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar("x" + i) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar("y" + i) ).toList
      val equalities = listX.zip(listY).foldRight(List[FOLFormula]()) {
        case (p, acc) => 
          val eq = "="
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val conj = And(equalities)
      val name = fname
      val f1 = Function(name, listX)
      val f2 = Function(name, listY)
      val eq = "="
      val last_eq = Atom(eq, List(f1, f2))
      val matrix = Imp(conj, last_eq)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val fname = getFunctionName(f.last)
    val n = f.size - 1
    val eq_congr = gen_eq_congr(n, fname)
    
    // Fixing the order of equalities
    val (args1, args2) = getArgsLst(f.last)
    val pairs = args1.zip(args2)
    val (correct, symm) = fixOrder(pairs, f)
    val instance = reverseCNF(correct)
    
    ((eq_congr, List(instance)) :: symm)
  }

  // Assuming all the antecedents of the implication are in order:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn) ^ p(x0...xn)  ->  p(y0...yn) )
  // in veriT is *always* 
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), not p(x0...xn), p(y0...yn) )
  // or
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), p(x0...xn), not p(y0...yn) )
  def getEqCongrPredInstances(f: List[FOLFormula]) : List[Instances] = {

    def getPredName(f: FOLFormula) = f match {
      case Atom(p, _) => p.toString
      case Neg(Atom(p, _)) => p.toString
    }

    def getArgsLst(p1: FOLFormula, p2: FOLFormula) = (p1, p2) match {
      case ( Neg(Atom(_, args1)), Atom(_, args2) ) => (args1, args2)
      case ( Atom(_, args1), Neg(Atom(_, args2)) ) => (args2, args1)
    }

    // Generate the eq_congruent_pred with the right number of literals
    def gen_eq_congr_pred(n: Int, pname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar("x" + i) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar("y" + i) ).toList
      val equalities = listX.zip(listY).foldRight(List[FOLFormula]()) {
        case (p, acc) => 
          val eq = "="
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val name = pname
      val p1 = Atom(name, listX)
      val p2 = Atom(name, listY)
      val conj = And(equalities :+ p1)
      val matrix = Imp(conj, p2)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val pname = getPredName(f.last)
    val n = f.size - 2
    val eq_congr_pred = gen_eq_congr_pred(n, pname)
    
    // Fixing the order of equalities
    val (args1, args2) = getArgsLst(f(f.length-2), f(f.length-1))
    val pairs = args1.zip(args2)
    val (correct, symm) = fixOrder(pairs, f)
    val instance = reverseCNF(correct)
    
    ((eq_congr_pred, List(instance)) :: symm)
  }

  def read(filename : String) : (Seq[ExpansionTree], Seq[ExpansionTree]) = {
    parseAll(proof, new FileReader(filename)) match {
      case Success(r, _) => r
      case Failure(msg, next) => 
        println("FILE: " + filename)
        println("VeriT parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column)
        throw new Exception("VeriT parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column)
      case Error(msg, next) => 
        println("FILE: " + filename)
        println("VeriT parsing: syntax error " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column)
        throw new Exception("VeriT parsing: syntax error " + msg + "\nat " + next.pos.line + " and column " + next.pos.column)
    }
  }

  // Each list of formulas corresponds to the formulas occurring in one of the axioms.
  def proof : Parser[(Seq[ExpansionTree], Seq[ExpansionTree])] = rep(line) ^^ {
    case list => 
      val allpairs = list.flatten
      
      // Join the instances of the same quantified formula
      val (input, axioms) = allpairs.partition(p => p._2 == Nil)
      val keys = axioms.map(p => p._1).distinct 
      val joinedInst = keys.foldLeft(List[Instances]()) {case (acc, f) =>
        val keyf = axioms.filter(p => p._1 == f)
        val allInst = keyf.foldLeft(List[FOLFormula]()) ((acc, p) => p._2 ++ acc)
        (f, allInst.distinct) :: acc
      }
      // Transform all pairs into expansion trees
      val inputET = input.map(p => qFreeToExpansionTree(p._1))
      val axiomET = joinedInst.map(p => prenexToExpansionTree(p._1, p._2))
      val ant = axiomET ++ inputET

      val cons = List()
      (ant.toSeq, cons.toSeq)
  }
  
  def line : Parser[List[Instances]] = useless | ruleDesc 

  // For type-matching purposes...
  def useless : Parser[List[Instances]] = (success | unsat | header) ^^ { 
    case s => Nil }
  
  // Dummy strings that should be ignored
  def success : Parser[String] = "success"
  def unsat : Parser[String] = "unsat"
  def header : Parser[String] = "verit dev - the VERI(T) theorem prover (UFRN/LORIA)."
  
  def ruleDesc : Parser[List[Instances]] = "(set" ~ label ~ "(" ~> rule <~ "))"
  def label : Parser[String] = ".c" ~ """\d+""".r ^^ { case s1 ~ s2 => s1 ++ s2 }

  def rule : Parser[List[Instances]] = axiom | innerRule
  
  def axiom : Parser[List[Instances]] = input | eq_reflexive | eq_transitive | eq_congruence | eq_congruence_pred
  
  def input : Parser[List[Instances]] = "input" ~> conclusion ^^ { case forms =>
    //println("Parsed input formulas")
    forms.map(f => (f, Nil))
  }
  
  def eq_reflexive : Parser[List[Instances]] = "eq_reflexive" ~> conclusion ^^ {
    case c => 
      //println("eq_reflexive"); 
      getEqReflInstances(c)
  }
  def eq_transitive : Parser[List[Instances]] = "eq_transitive" ~> conclusion ^^ {
    case c => 
      //println("eq_transitive"); 
      getEqTransInstances(c)
  }
  def eq_congruence : Parser[List[Instances]] = "eq_congruent" ~> conclusion ^^ {
    case c => 
      //println("eq_congruent"); 
      getEqCongrInstances(c)
  }
  def eq_congruence_pred : Parser[List[Instances]] = "eq_congruent_pred" ~> conclusion ^^ {
    case c => 
      //println("eq_congruent_pred"); 
      getEqCongrPredInstances(c)
  }

  def innerRule : Parser[List[Instances]] = resolution | and | and_pos | or | tmp_distinct_elim | tmp_alphaconv | tmp_let_elim
  
  // Rules that I don't care
  def resolution : Parser[List[Instances]] = "resolution" ~> premises <~ conclusion
  def and : Parser[List[Instances]] = "and" ~> premises <~ conclusion
  def and_pos : Parser[List[Instances]] = "and_pos" ~> conclusion  ^^ { case _ => Nil }
  def or : Parser[List[Instances]] = "or" ~> premises <~ conclusion
  def tmp_distinct_elim : Parser[List[Instances]] = "tmp_distinct_elim" ~> premises <~ conclusion
  // TODO: what to do with these???
  def tmp_alphaconv : Parser[List[Instances]] = "tmp_alphaconv" ~> premises <~ conclusion
  def tmp_let_elim : Parser[List[Instances]] = "tmp_let_elim" ~> premises <~ conclusion
  
  // I don't care about premises. I only use the leaves
  def premises : Parser[List[Instances]] = ":clauses (" ~ rep(label) ~ ")" ^^ { case _ => Nil}
  def conclusion : Parser[List[FOLFormula]] = ":conclusion (" ~> rep(expression) <~ ")"
 
  def expression : Parser[FOLFormula] = formula | let
  def formula : Parser[FOLFormula] = andFormula | orFormula | notFormula | pred
  
  def term : Parser[FOLTerm] = variable | function 
  def variable : Parser[FOLTerm] = name ^^ { case n => FOLVar(n) }
  def function : Parser[FOLTerm] = "(" ~> name ~ rep(term) <~ ")" ^^ {
    case name ~ args => 
      Function(name, args)
  }

  def andFormula : Parser[FOLFormula] = "(and" ~> rep(formula) <~ ")" ^^ { 
    case flst => And(flst)
  }
  def orFormula : Parser[FOLFormula] = "(or" ~> rep(formula) <~ ")" ^^ { 
    case flst => Or(flst)
  }
  def notFormula : Parser[FOLFormula] = "(not" ~> formula <~ ")" ^^ { 
    case f => Neg(f)
  }
  def pred : Parser[FOLFormula] = "(" ~> name ~ rep(term) <~ ")" ^^ { 
    case name ~ args => 
      Atom(name, args)
  }

  // Syntax of let-expressions:
  // (let (v1 t1) ... (vn tn) exp)
  // which is equivalent to the lambda-expression:
  // (\lambda v1 ... vn exp) t1 ... tn
  def let : Parser[FOLFormula] = "(" ~> "let" ~> "(" ~> rep(binding) ~ ")" ~ expression <~ ")" ^^ {
    case bLst ~ ")" ~ f => 
    val lambda_exp = bLst.foldRight(f) {
      case ((v, t), exp) => FOLApp(FOLAbs(v.asInstanceOf[FOLVar], exp), t).asInstanceOf[FOLFormula]
    }.asInstanceOf[FOLFormula]
    betaNormalize(lambda_exp)
  }

  def binding : Parser[(FOLTerm, FOLTerm)] = "(" ~> variable ~ term <~ ")" ^^ {
    case v ~ t => (v, t)
  }
  
  def name : Parser[String] = """[^ ():]+""".r

}
