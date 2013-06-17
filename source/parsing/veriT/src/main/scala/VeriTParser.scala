package at.logic.parsing.veriT

import scala.util.parsing.combinator._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, prenexToExpansionTree, qFreeToExpansionTree}
import java.io.FileReader

object VeriTParser extends RegexParsers {

  def read(filename : String) : (Seq[ExpansionTree], Seq[ExpansionTree]) = {
    parse(finalResult, new FileReader(filename)) match {
      case Success(r, _) => r
      case Failure(msg, _) => throw new Exception("Failure in veriT parsing: " + msg)
      case Error(msg, _) => throw new Exception("Error in veriT parsing: " + msg)
    }
  }

  def eq_reflexive_toExpTree(f : List[FOLFormula]) : ExpansionTree = {
    val x = FOLVar(VariableStringSymbol("x"))
    val eq = ConstantStringSymbol("=")
    val eq_refl = AllVar(x, Atom(eq, List(x, x)))
    prenexToExpansionTree(eq_refl, f)
  }

  // Assuming all the antecedents of the implication are in order:
  // ( =(x0, x1)  ^  =(x1, x2)  ^ ... ^  =(xn-1, xn)  ->  =(x0, xn) )
  // in veriT is *always* ( not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) )
  def eq_transitive_toExpTree(l : List[FOLFormula]) : ExpansionTree = {
    val x = FOLVar(VariableStringSymbol("x"))
    val y = FOLVar(VariableStringSymbol("y"))
    val z = FOLVar(VariableStringSymbol("z"))
    val eq = ConstantStringSymbol("=")
    val eq1 = Atom(eq, List(x, y))
    val eq2 = Atom(eq, List(y, z))
    val eq3 = Atom(eq, List(x, z))
    val imp = Imp(And(eq1, eq2), eq3)
    val eq_trans = AllVar(x, AllVar(y, AllVar(z, imp)))

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
        // Checking all possible cases of atom ordering, i.e.:
        // x=y ^ y=z -> x=z
        // x=y ^ z=y -> x=z
        // y=x ^ y=z -> x=z
        // ...
        case Neg(Atom(eq1, List(x2, x3))) if x1 == x2 =>
          val newc = Neg(Atom(eq, List(x0, x3)))
          // Instances
          val f1 = FOLSubstitution(eq_trans, x, x0)
          val f2 = FOLSubstitution(f1, y, x1) // or x2, should be the same
          val f3 = FOLSubstitution(f2, z, x3)

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) if x1 == x3 =>
          val newc = Neg(Atom(eq, List(x0, x2)))
          // Instances
          val f1 = FOLSubstitution(eq_trans, x, x0)
          val f2 = FOLSubstitution(f1, y, x1) // or x3, should be the same
          val f3 = FOLSubstitution(f2, z, x2)

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) if x0 == x2 =>
          val newc = Neg(Atom(eq, List(x1, x3)))
          // Instances
          val f1 = FOLSubstitution(eq_trans, x, x1)
          val f2 = FOLSubstitution(f1, y, x0) // or x2, should be the same
          val f3 = FOLSubstitution(f2, z, x3)

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) if x0 == x3 =>
          val newc = Neg(Atom(eq, List(x2, x1)))
          // Instances
          val f1 = FOLSubstitution(eq_trans, x, x1)
          val f2 = FOLSubstitution(f1, y, x0) // or x3, should be the same
          val f3 = FOLSubstitution(f2, z, x2)

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) => throw new Exception("ERROR: the conclusion of the previous terms have" +  
          " no literal in common with the next one. Are the literals out of order?")

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
    prenexToExpansionTree(eq_trans, instances)
  }

  def eq_congr_toExpTree(f: List[FOLFormula]) : ExpansionTree = {
    
    def getFunctionName(f: FOLFormula) : String = f match {
      case Imp(_, Atom(eq, List(f1, _))) => f1 match {
          case Function(ConstantStringSymbol(n), _) => n 
      }
    }

    // Generate the eq_congruent formula with the right number of literals
    def gen_eq_congr(n: Int, fname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("x" + i)) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("y" + i)) ).toList
      val equalities = listX.zip(listY).foldLeft(List[FOLFormula]()) {
        case (acc, p) => 
          val eq = ConstantStringSymbol("=")
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val conj = Utils.andN(equalities)
      val name = ConstantStringSymbol(fname)
      val f1 = Function(name, listX)
      val f2 = Function(name, listY)
      val eq = ConstantStringSymbol("=")
      val last_eq = Atom(eq, List(f1, f2))
      val matrix = Imp(conj, last_eq)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val instance = Utils.reverseCNF(f)
    val fname = getFunctionName(instance)
    val n = f.size - 1
    val eq_congr = gen_eq_congr(n, fname)
    
    prenexToExpansionTree(eq_congr, List(instance))
  }

  def eq_congr_pred_toExpTree(f: List[FOLFormula]) : ExpansionTree = {

    def getPredName(f: FOLFormula) : String = f match {
      case Imp(_, Atom(p, _)) => p match {
          case ConstantStringSymbol(n) => n 
      }
    }

    // Generate the eq_congruent_pred with the right number of literals
    def gen_eq_congr_pred(n: Int, pname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("x" + i)) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("y" + i)) ).toList
      val equalities = listX.zip(listY).foldLeft(List[FOLFormula]()) {
        case (acc, p) => 
          val eq = ConstantStringSymbol("=")
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val conj = Utils.andN(equalities)
      val name = ConstantStringSymbol(pname)
      val p1 = Atom(name, listX)
      val p2 = Atom(name, listY)
      val matrix = Imp(And(conj, p1), p2)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val instance = Utils.reverseCNF(f)
    val pname = getPredName(instance)
    val n = f.size - 2
    val eq_congr_pred = gen_eq_congr_pred(n, pname)
    
    prenexToExpansionTree(eq_congr_pred, List(instance))
  }

  // Each list of formulas corresponds to the formulas occurring in one of the axioms.
  def finalResult : Parser[(Seq[ExpansionTree], Seq[ExpansionTree])] = rep(line) ^^ {
    case list => 
      val ant = list.flatten
      val cons = List()
      (ant.toSeq, cons.toSeq)
  }
  
  def line : Parser[List[ExpansionTree]] = useless | ruleDesc
  
  // For type-matching purposes...
  def useless : Parser[List[ExpansionTree]] = (success | unsat | header) ^^ { 
    case s => Nil }
  
  // Dummy strings that should be ignored
  def success : Parser[String] = "success"
  def unsat : Parser[String] = "unsat"
  def header : Parser[String] = "verit dev - the VERI(T) theorem prover (UFRN/LORIA)."
  
  def ruleDesc : Parser[List[ExpansionTree]] = "(set" ~ label ~ "(" ~> rule <~ "))"
  def label : Parser[String] = ".c" ~ """\d+""".r ^^ { case s1 ~ s2 => s1 ++ s2 }

  def rule : Parser[List[ExpansionTree]] = axiom | innerRule
  
  def axiom : Parser[List[ExpansionTree]] = input | eq_reflexive | eq_transitive | eq_congruence | eq_congruence_pred
  
  def input : Parser[List[ExpansionTree]] = "input" ~> conclusion ^^ { case forms =>
    forms.map(f => qFreeToExpansionTree(f))
  }
  
  def eq_reflexive : Parser[List[ExpansionTree]] = "eq_reflexive" ~> conclusion ^^ {
    case c => List( eq_reflexive_toExpTree(c) )
  }
  def eq_transitive : Parser[List[ExpansionTree]] = "eq_transitive" ~> conclusion ^^ {
    case c => List( eq_transitive_toExpTree(c) )
  }
  def eq_congruence : Parser[List[ExpansionTree]] = "eq_congruent" ~> conclusion ^^ {
    case c => List( eq_congr_toExpTree(c) )
  }
  def eq_congruence_pred : Parser[List[ExpansionTree]] = "eq_congruent_pred" ~> conclusion ^^ {
    case c => List( eq_congr_pred_toExpTree(c) )
  }

  def innerRule : Parser[List[ExpansionTree]] = resolution | and | and_pos | or
  
  // Rules that I don't care
  def resolution : Parser[List[ExpansionTree]] = "resolution" ~> premises <~ conclusion
  def and : Parser[List[ExpansionTree]] = "and" ~> premises <~ conclusion
  def and_pos : Parser[List[ExpansionTree]] = "and_pos" ~> conclusion  ^^ { case _ => Nil }
  def or : Parser[List[ExpansionTree]] = "or" ~> premises <~ conclusion
  
  // I don't care about premises. I only use the leaves
  def premises : Parser[List[ExpansionTree]] = ":clauses (" ~ rep(label) ~ ")" ^^ { case _ => Nil}
  def conclusion : Parser[List[FOLFormula]] = ":conclusion (" ~> rep(formula) <~ ")"
 
  def formula : Parser[FOLFormula] = andFormula | orFormula | notFormula | pred
  def term : Parser[FOLTerm] = name ~ rep(term) ^^ {
    case name ~ args => 
      val n = ConstantStringSymbol(name) 
      Function(n, args)
  }

  def andFormula : Parser[FOLFormula] = "(and" ~> rep(formula) <~ ")" ^^ { 
    case flst => Utils.andN(flst) 
  }
  def orFormula : Parser[FOLFormula] = "(or" ~> rep(formula) <~ ")" ^^ { 
    case flst => Utils.orN(flst) 
  }
  def notFormula : Parser[FOLFormula] = "(not" ~> formula <~ ")" ^^ { 
    case f => Neg(f) 
  }
  def pred : Parser[FOLFormula] = "(" ~> name ~ rep(term) <~ ")" ^^ { 
    case name ~ args => 
      val n = ConstantStringSymbol(name)
      Atom(n, args) 
  }
  
  def name : Parser[String] = """[^ ():]+""".r

}