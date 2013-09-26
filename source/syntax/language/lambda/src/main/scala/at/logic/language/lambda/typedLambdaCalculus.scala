/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language.lambda.typedLambdaCalculus

import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._

// Collects all methods that operate on LambdaExpressions
abstract class LambdaExpression {
  
  // Expression type [should it be here?]
  def exptype: TA

  // Syntactic equality
  def syntaxEquals(e: LambdaExpression): Boolean

  // List of free variables
  def freeVariables: List[Var] = getFreeVariables(List())
  
  private def getFreeVariables(bound: List[Var]) : List[Var] = this match {
    case v : Var =>
      if (!bound.contains(v)) List(v)
      else List()
    case Cons(_) => List()
    case App(exp, arg) => exp.getFreeVariables(bound) ++ arg.getFreeVariables(bound)
    case Abs(v, exp) => exp.getFreeVariables(v :: bound)
  }
  
}

// Defines the elements that generate lambda-expressions: variables,
// applications and abstractions (and constants).
class Var(val sym: SymbolA, val exptype: TA) extends LambdaExpression {

  // sym is not accessible outside because we do not want the user
  // knowing about this symbol stuff. If he asks for the name of the variable,
  // it is a string that he should get.
  def name : String = sym match {
    case StringSymbol(s) => s
    case VariantSymbol(s, _) => s
    case _ => throw new Exception("Unexpected type.")
  }

  // Syntactic equality
  def syntaxEquals(e: LambdaExpression) = e match {
    case Var(n, t) => (n == name && t == exptype)
    case _ => false
  }

  // Alpha-equality
  // Two free variables are *not* alpha-equivalent if they don't have the same name and type.
  override def equals(a: Any) = a match {
    case Var(n, t) => (n == this.name && t == exptype)
    case _ => false
  }
    
  // Printing
  override def toString() = "Var(" + name + "," + exptype + ")"
}
object Var {
  def apply(name: String, exptype: TA) = new Var(StringSymbol(name), exptype)
  def unapply(e: LambdaExpression) = e match {
    case v : Var => v.sym match {
      case StringSymbol(n) => Some((n, v.exptype))
      case VariantSymbol(n, i) => Some((n + i.toString, v.exptype))
    }
    case _ => None
  }
}

class Cons(val sym: SymbolA, val exptype: TA) extends LambdaExpression {

  // sym is not accessible outside because we do not want the user
  // knowing about this symbol stuff. If he asks for the name of the variable,
  // it is a string that he should get.
  def name : String = sym match {
    case StringSymbol(s) => s
    case VariantSymbol(s, _) => s
    case _ => throw new Exception("Unexpected type.")
  }

  // Syntactic equality
  def syntaxEquals(e: LambdaExpression) = e match {
    case Cons(n, t) => (n == name && t == exptype)
    case _ => false
  }
    
  // Alpha-equality
  // Two constants are *not* alpha-equivalent if they don't have the same name and type.
  override def equals(a: Any) = a match {
    case Cons(n, t) => (n == name && t == exptype)
    case _ => false
  }
  
  // Printing
  override def toString() = "Cons(" + name + "," + exptype + ")"

}
object Cons {
  def apply(name: String, exptype: TA) = new Cons(StringSymbol(name), exptype)
  def unapply(e: LambdaExpression) = e match {
    case c : Cons => c.sym match {
      case StringSymbol(n) => Some((n, c.exptype))
      case _ => None
    }
    case _ => None
  }
}

class App(val function: LambdaExpression, val arg: LambdaExpression) extends LambdaExpression {
  
  // Making sure that if f: t1 -> t2 then arg: t1
  require({
    function.exptype match {
      case ->(in,out) => {
        if (in == arg.exptype) true
        else false
      }
      case _ => false
    }
  }, "Types don't fit while constructing application " + function + " " + arg)

  // Application type (if f: t1 -> t2 and arg: t1 then t2)
  def exptype: TA = {
    function.exptype match {
        case ->(in,out) => out
    }
  }
  
  // Syntactic equality
  def syntaxEquals(e: LambdaExpression) = e match {
    case App(a,b) => (a.syntaxEquals(function) && b.syntaxEquals(arg) && e.exptype == exptype)
    case _ => false
  }

  // Alpha-equality
  // An application is alpha-equivalent if its terms are alpha-equivalent.
  override def equals(a: Any) = a match {
    case App(e1, e2) => e1 == function && e2 == arg
    case _ => false
  }

  // Printing
  override def toString() = "App(" + function + "," + arg + ")"
}
object App {
  def apply(f: LambdaExpression, a: LambdaExpression) = new App(f, a)
  def unapply(e: LambdaExpression) = e match {
    case a : App => Some((a.function, a.arg))
    case _ => None
  }
}
// This is to be used only for facilitating the construction of terms with
// multiple applications. It should not be used in a match.
object AppN {
  def apply(function: LambdaExpression, arguments:List[LambdaExpression]): LambdaExpression = arguments match {
    case Nil => function
    case x::ls => apply(App(function, x), ls)
  }
}

class Abs(val variable: Var, val term: LambdaExpression) extends LambdaExpression {

  // Abstraction type construction based on the types of the variable and term
  def exptype: TA = ->(variable.exptype, term.exptype)
  
  // Syntactic equality
  def syntaxEquals(e: LambdaExpression) = e match {
    case Abs(v, exp) => (v.syntaxEquals(variable) && exp.syntaxEquals(term) && e.exptype == exptype)
    case _ => false
  }

  // Alpha-equality
  // Two abstractions are alpha-equivalent if the terms are equivalent up to the
  // renaming of variables.
  override def equals(a: Any) = a match {
    case Abs(v, t) =>
      if ( v == variable) { t == term }
      else if (v.exptype == variable.exptype) {
        val blackList = term.freeVariables ++ t.freeVariables
        val freshVar = getRenaming(Var("alpha", v.exptype), blackList)
        // t[v\freshVar] == term[variable\freshVar]
        val t1 = substitute(t, v, freshVar) 
        val t2 = substitute(term, variable, freshVar)
        t1 == t2
      }
      else false
    case _ => false
  }

  // Printing
  override def toString() = "Abs(" + variable + "," + term + ")"
}
object Abs {
  def apply(v: Var, t: LambdaExpression) = new Abs(v, t)
  def unapply(e: LambdaExpression) = e match {
    case a : Abs => Some((a.variable, a.term))
    case _ => None
  }
}
// This is to be used only for facilitating the construction of terms with
// multiple abstractions. It should not be used in a match.
object AbsN {
  def apply(variables: List[Var], expression: LambdaExpression): LambdaExpression = variables match {
    case Nil => expression
    case x::ls => Abs(x, apply(ls, expression))
  }
}

// Renames the variables in 'toRename' such that the new names do not clash
// with variables in 'blackList'.
object getRenaming {
  def apply(toRename: Var, blackList: List[Var]) : Var = apply(List(toRename), blackList).head
  def apply(toRename: List[Var], blackList: List[Var]) : List[Var] = toRename match {
    case v :: tl => 
      if ( blackList.exists(e => e.syntaxEquals(v)) ) {
        val newV = v.sym match {
          case StringSymbol(n) => new Var(VariantSymbol(n, 0), v.exptype)
          case VariantSymbol(n, i) => new Var(VariantSymbol(n, i+1), v.exptype)
        }
        // Put back in the list to check if the renaming does not clash again.
        getRenaming(newV::tl, blackList)
      }
      else v :: ( getRenaming(tl, blackList) )
    case Nil => List()
  }
}

// Substitution (capture-avoinding)
// as in http://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions
object substitute {
  def apply(t: LambdaExpression, x: Var, u: LambdaExpression) : LambdaExpression = t match {
    case Var(_, _) if t == x => u
    case Var(_, _) if t != x => t
    case App(t1, t2) => App(substitute(t1, x, u), substitute(t2, x, u))
    case Abs(v, t1) =>
      val fv = u.freeVariables
      if (v == x) t
      else if (!fv.contains(v)) {
        Abs(v, substitute(t1, x, u))
      }
      else {
        val freshVar = getRenaming(v, fv)
        val newTerm = substitute(t1, v, freshVar)
        Abs(freshVar, substitute(newTerm, x, u))
      }
  }
}
