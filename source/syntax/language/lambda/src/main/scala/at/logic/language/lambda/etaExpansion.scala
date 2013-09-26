/*
 * etaExpansion.scala
 *
 */

package at.logic.language.lambda.etaExpansion

import at.logic.language.lambda.symbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
  
// Transforms a function f: i0 -> ... -> in -> o into
// \lambda x0:i0. ... \lambda xn:in f x0 ... xn
// i.e. adds the lambda abstraction and new variables.
// Note that etaExpantion is applied only to expressions in beta-normal form.
object EtaExpand {
  def apply(term: LambdaExpression) : LambdaExpression = apply(term, List())
  def apply(term: LambdaExpression, disallowedVars: List[Var]) : LambdaExpression = term match {
    case Var(_, exptype) => exptype match {
      case Ti() => term
      case To() => term
      case FunctionType(_, args) => {
        val binders: List[Var] = args.map(z => {
          val newVar = Var("eta", z) // Creating a new var of appropriate type
          getRenaming(newVar, disallowedVars) // Rename if needed
        })
        val dv = disallowedVars ++ binders
        AbsN(binders, AppN(term, binders.map((z => apply(z, dv)))))
      }
    }

    case App(m,n) => term.exptype match {
      case Ti() => term
      case To() => term
      case FunctionType(_, args) => {
        val binders: List[Var] = args.map(z => {
          val newVar = Var("eta", z) // Creating a new var of appropriate type
          getRenaming(newVar, disallowedVars) // Rename if needed
        })
        val dv = disallowedVars ++ binders
        AbsN(binders, AppN(App(m,apply(n, dv)), binders.map((z => apply(z, dv)))))
      }
    }

    case Abs(x,t) => Abs(x, apply(t, disallowedVars))
  }
}


