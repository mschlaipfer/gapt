/*
 * The definition of Indexed proposition is taken from:
 * A Schemata Calculus for Propositional Logic by Vincent Aravantinos, Ricardo Caferra, and Nicolas Peltier
 *
 */

package at.logic.language.schema

import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.{HOLFormula, HOLExpression, HOLVar, HOLConst, HOLApp, HOLAbs}
import at.logic.language.hol.logicSymbols._
import at.logic.language.schema.logicSymbols._

trait SchemaExpression extends HOLExpression {
  
  //TODO : needs improvement for the step case
  def unfoldSTerm: SchemaExpression = {
    val k = IntVar("k")
    val x = foVar("x")
    this match {
      case sTerm(func, i, arg) if dbTRS.map.contains(func) => {
        if (i == IntZero()) {
          val base = dbTRS.map.get(func).get._1._2
          val new_map = Map[Var, HOLExpression]() + Pair(x, arg.head)
          //val subst = new SchemaSubstitution2[HOLExpression](new_map)
          val subst = Substitution(new_map)
          subst[SchemaExpression](base)
        }
        else if (i == k) this
        else i match {
          case Succ(_) => dbTRS.map.get(func).get._2._2 match {
            case foTerm(name, arg1) => foTerm(name, sTerm(func, Pred(i.asInstanceOf[IntegerTerm]), arg).unfoldSTerm::Nil)
          }
          case _ => 
            val j = i.unfoldSINDTerm
            sTerm(func, j, arg).unfoldSTerm
        }
      }
      case sTerm(func, i, arg) => this
      case foTerm(holvar, arg) => foTerm(holvar, arg.unfoldSTerm::Nil)
      case _ => this
    }
  }

  def unfoldSINDTerm : SchemaExpression = {
    val k = IntVar("k")
    this match {
      case sIndTerm(func, i) if dbTRS.map.contains(func) => {
        if (i == IntZero()) dbTRS.map.get(func).get._1._2
        else if (i == k) this
        else {
          val step = dbTRS.map.get(func).get._2._2
          val new_map = Map[Var, SchemaExpression]() + Pair(k, Pred(i.asInstanceOf[IntegerTerm]))
          //val subst = new SchemaSubstitution2[HOLExpression](new_map)
          val subst = Substitution(new_map)
          subst(step)
        }
      }
      case _ => this
    }
  }

  override def factory: FactoryA = SchemaFactory
}

trait SchemaFormula extends SchemaExpression with HOLFormula {

  def unfoldSFormula : SchemaFormula = this match {
    case Atom(name, args) => Atom(name, args.map(t => t.unfoldSTerm))
    case Imp(f1, f2) => Imp(f1.unfoldSFormula, f2.unfoldSFormula)
    case ExVar(v, f) => ExVar(v, f.unfoldSFormula)
    case AllVar(v, f) => AllVar(v, f.unfoldSFormula)
    case _ => f
  }

  override def isAtom : Boolean = this match {
    case Atom(_,_) => true
    case IndexedPredicate(_,_) => true
    case _ => false
  }
}

/************************* BASIC DATATYPES **************************/

class SchemaVar protected[schema] (sym: SymbolA, exptype: TA) extends HOLVar(sym, exptype) with SchemaExpression 
object SchemaVar {
  def apply(name: String, exptype: TA) = exptype match {
    case To => new SchemaVar(StringSymbol(name), exptype) with SchemaFormula
    case Tindex => new IntVar(StringSymbol(name))
    case _ => new SchemaVar(StringSymbol(name), exptype)
  }
  def unapply(exp: SchemaExpression) = exp match {
    case v: SchemaVar => Some( (v.name, v.exptype) )
    case _ => None
  }
}

class SchemaConst protected[schema] (sym: SymbolA, exptype: TA) extends HOLConst(sym, exptype) with SchemaExpression
object SchemaConst {
  def apply(name: String, exptype: TA) = exptype match {
    case To => new SchemaConst(StringSymbol(name), exptype) with SchemaFormula
    case Tindex => new IntConst(StringSymbol(name))
    case _ => new SchemaConst(StringSymbol(name), exptype)
  }
  def apply(name: String, exptype: String) = SchemaConst(name, Type(exptype))
  def unapply(exp: SchemaExpression) = exp match {
    case c: SchemaConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

class SchemaApp private[schema] (function: SchemaExpression, arg: SchemaExpression) extends HOLApp(function, arg) with SchemaExpression
object SchemaApp {
  def apply(function: SchemaExpression, argument: SchemaExpression) = function.exptype match {
    case ->(_, To) => new SchemaApp(function, argument) with SchemaFormula
    case _ => new SchemaApp(function, argument)
  }
  def apply(function: SchemaExpression, arguments: List[SchemaExpression]) : SchemaExpression = arguments match {
    case Nil => function
    case h :: tl => apply(SchemaApp(function, h), tl)
  }
  def unapply(e: SchemaExpression) = e match {
    case a: SchemaApp => Some( (a.function.asInstanceOf[SchemaExpression], a.arg.asInstanceOf[SchemaExpression]) )
    case _ => None
  }
}

class SchemaAbs private[schema] (variable: IntVar, expression: SchemaExpression) extends HOLAbs(variable, expression) with SchemaExpression
object SchemaAbs {
  def apply(v: IntVar, e: SchemaExpression) = new SchemaAbs(v, e)
  def unapply(e: SchemaExpression) = e match {
    case a: SchemaAbs => Some( (a.variable.asInstanceOf[IntVar], a.term.asInstanceOf[SchemaExpression]) )
    case _ => None
  }
}

/******************** SPECIAL INTEGERS ************************************/

trait IntegerTerm extends SchemaExpression { require( exptype == Tindex ) }

class IntVar (sym: SymbolA) extends SchemaVar(sym, Tindex) with IntegerTerm {
  override def toString = name.toString+":"+exptype.toString
}
object IntVar {
  def apply(name: String) = new IntVar(StringSymbol(name))
  def unapply(t: IntegerTerm) = t match {
    case i: IntVar => Some(i.name)
    case _ => None
  }
}

class IntConst(sym: SymbolA) extends SchemaConst(sym, Tindex) with IntegerTerm

case class IntZero() extends SchemaConst(StringSymbol("0"), Tindex) with IntegerTerm

/**************************************************************************/

object IndexedPredicate {
  def apply(name: String, indexTerms: List[SchemaExpression]): SchemaFormula = {
    val pred = SchemaConst( name, FunctionType( To, indexTerms.head.exptype::Nil ) )
    SchemaApp(pred, indexTerms.head::Nil).asInstanceOf[SchemaFormula]
  }
  def apply(name: String, indexTerm: IntegerTerm): SchemaFormula = apply(sym, indexTerm::Nil)

  def unapply(e: SchemaExpression) = e match {
    case AppN(f : HOLConst with Schema, ts) if ts.forall( t => t.exptype == Tindex ) && e.exptype == To => Some((f, ts))
    case _ => None
  }
}

class indexedFOVar(val sym: SymbolA, val index: HOLExpression) extends HOLVar(sym, Ti) {
  override def toString = name.toString+"("+index+")"+":"+exptype.toString
  override def equals(a: Any): Boolean = a match {
    case v:indexedFOVar if v.name.toString() == this.name.toString() && v.index == this.index => true
    case _ => false
  }
}
object indexedFOVar {
  def apply(name: String, i: HOLExpression): HOLVar = new indexedFOVar(StringSymbol(name), i)
  def unapply(s: HOLExpression) = s match {
    case v: indexedFOVar => Some(v.name, v.index)
    case _ => None
  }
}

class indexedOmegaVar(val sym: SymbolA, val index: HOLExpression) extends HOLVar(sym, Tindex) {
  override def toString = name.toString+"("+index+")"+":"+exptype.toString
  override def equals(a: Any): Boolean = a match {
    case v:indexedOmegaVar if v.name == this.name && v.index == this.index => true
    case _ => false
  }
}
object indexedOmegaVar {
  def apply(name: String, i: SchemaExpression): HOLVar = {
    new indexedOmegaVar(StringSymbol(name), i)
  }
  def unapply(s: SchemaExpression) = s match {
    case v: indexedOmegaVar => Some(v.name, v.index)
    case _ => None
  }
}

class foVar(sym: SymbolA) extends SchemaVar(sym, Ti) {
  override def equals(a: Any): Boolean = a match {
    case v:foVar if v.name.toString() == this.name.toString() => true
    case _ => false
  }
}
object foVar {
  def apply(name: String) = new foVar(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case v: foVar => Some(v.name, Ti)
    case _ => None
  }
}

//first-order constant
class foConst(sym: SymbolA) extends SchemaConst(sym, Ti) {
  override def equals(a: Any): Boolean = a match {
    case v:foConst if v.name.toString() == this.name.toString() => true
    case _ => false
  }
}
object foConst {
  def apply(name: String) = new foConst(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case c: foConst => Some(c.name, c.exptype)
    case _ => None
  }
}

//first-order variable of type ω
class fowVar(sym: SymbolA) extends SchemaVar(sym, Tindex) {
  override def equals(a: Any): Boolean = a match {
    case v:fowVar if v.name.toString() == this.name.toString() => true
    case _ => false
  }
}
object fowVar {
  def apply(name: String) = new fowVar(StringSymbol(name))
  def unapply(t: SchemaExpression) = t match {
    case v: fowVar => Some(v.name, v.exptype)
    case _ => None
  }
}

/*************** OPERATORS *****************/

case object BottomC extends SchemaConst(BottomSymbol, To) with SchemaFormula
case object TopC extends SchemaConst(BottomSymbol, To) with SchemaFormula
case object NegC extends SchemaConst(NegSymbol, ->(To, To))
case object AndC extends SchemaConst(AndSymbol, ->(To, ->(To, To)))
case object OrC extends SchemaConst(OrSymbol, ->(To, ->(To, To)))
case object ImpC extends SchemaConst(ImpSymbol, ->(To, ->(To, To)))

// Schema-specific objects
case object BigAndC extends SchemaConst(BigAndSymbol, ->(->(Tindex, To), ->(Tindex, ->(Tindex, To))))
case object BigOrC extends SchemaConst(BigOrSymbol, ->(->(Tindex, To), ->(Tindex, ->(Tindex, To))))
case object BiggerThanC extends SchemaConst(BiggerThanSymbol, ->(Tindex, ->(Tindex, To)))
case class LessThanC(e:TA) extends SchemaConst(LessThanSymbol, ->(Tindex, ->(Tindex, To)))
case class LeqC(e:TA) extends SchemaConst(LeqSymbol, ->(Tindex, ->(Tindex, To)))

object Neg {
  def apply(sub: SchemaFormula) = SchemaApp(NegC,sub).asInstanceOf[SchemaFormula]
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(NegC,sub) => Some( sub.asInstanceOf[SchemaFormula] )
    case _ => None
  }
}

object And {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaApp(SchemaApp(AndC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(AndC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Or {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaApp(SchemaApp(OrC,left),right)).asInstanceOf[SchemaFormula]
  def apply(fs: List[SchemaFormula]) : SchemaFormula = fs match {
    case Nil => BottomC
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(OrC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaApp(SchemaApp(ImpC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: SchemaExpression) = expression match {
      case SchemaApp(SchemaApp(ImpC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
      case _ => None
  }
}

object BigAnd {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm , end: IntegerTerm) : SchemaFormula =
    SchemaApp(BigAndC, iter::init::end::Nil).asInstanceOf[SchemaFormula]
  
  // TODO: recursive unapply?
  def unapply(exp : LambdaExpression) = exp match {
    case AppN(BigAndC, SchemaAbs(v, formula)::(init : IntegerTerm)::(end : IntegerTerm)::Nil) =>
      Some(v, formula, init, end)
    case _ => None
  }
}

object BigOr {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    SchemaApp(BigOrC, iter::init::end::Nil).asInstanceOf[SchemaFormula]

  // TODO: recursive unapply?
  def unapply(exp : LambdaExpression) = exp match {
    case AppN(BigOrC, SchemaAbs(v, formula)::(init : IntegerTerm)::(end : IntegerTerm)::Nil) =>
      Some(v, formula, init, end)
    case _ => None
  }
}

object BiggerThan {
  def apply(l: IntegerTerm, r: IntegerTerm) = SchemaApp(SchemaApp(BiggerThanC, l), r)
  def unapply(e: LambdaExpression) = e match {
    case SchemaApp(SchemaApp(BiggerThanC, l), r) => Some( (l, r) )
    case _ => None
  }
}

/** Should symbols be created for these operators also?? **/

object Succ extends SchemaConst(StringSymbol("s"), ->(Tindex, Tindex)) {
  override def toString = this match {
    case SchemaApp(Succ, t) => "s("+t.toString+")"
    case _ => "ERROR in Succ"
  }
  def apply(t: IntegerTerm): IntegerTerm  = SchemaApp(Succ, t)
  def apply(t: SchemaExpression): SchemaExpression  = SchemaApp(Succ, t)
  def unapply(p: SchemaExpression) = p match {
    case SchemaApp(Succ, t : IntegerTerm) => Some(t)
    case _ => None
  }
}

object Pred {
  def apply(t: IntegerTerm): IntegerTerm  =  t match {
    case Succ(t1) => t1
    case _ => throw new Exception("ERROR in Predecessor")
  }
}

//object representing a schematic atom: P(i:ω, args)
object Atom {
  def apply(head: SchemaVar, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]
  def apply(head: SchemaConst, args: List[SchemaExpression]): SchemaFormula = apply_(head, args).asInstanceOf[SchemaFormula]
  private def apply_(head: SchemaExpression, args: List[SchemaExpression]): SchemaExpression = args match {
    case Nil => head
    case t :: tl => apply_(SchemaApp(head, t), tl)
  }

  def unapply( expression: SchemaExpression ) = expression match {
    case SchemaApp(c: SchemaConst,_) if c.isLogicalSymbol => None
    case SchemaApp(SchemaApp(c: SchemaConst,_),_) if c.isLogicalSymbol => None
    case SchemaApp(_,_) if (expression.exptype == To) => Some( unapply_(expression) )
    case SchemaConst(_) if (expression.exptype == To) => Some( (expression, Nil) )
    case SchemaVar(_) if (expression.exptype == To) => Some( (expression, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: SchemaExpression) : (SchemaExpression, List[SchemaExpression]) = e match {
    case v: SchemaVar => (v, Nil)
    case c: SchemaConst => (c, Nil)
    case SchemaApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
  }
}


object lessThan {
  def apply(left: SchemaExpression, right: SchemaExpression) = {
    require(left.exptype == right.exptype)
    SchemaApp(SchemaApp(LessThanC(left.exptype), left),right).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(LessThanC(_),left),right) => Some( left, right )
    case _ => None
  }
}

object leq {
  def apply(left: SchemaExpression, right: SchemaExpression) = {
    require(left.exptype == right.exptype)
    SchemaApp(SchemaApp(LeqC(left.exptype), left),right).asInstanceOf[SchemaFormula]
  }
  def unapply(expression: SchemaExpression) = expression match {
    case SchemaApp(SchemaApp(LeqC(_),left),right) => Some( left,right )
    case _ => None
  }
}


object aTerm {
  def apply(name: SchemaConst, ind: IntegerTerm): IntegerTerm = {
    SchemaFactory.createApp(name, ind).asInstanceOf[IntegerTerm]
  }
}

// Create a var or const????
object foTerm {
  def apply(name: String, args: List[SchemaExpression]): SchemaExpression = {
    val v = SchemaVar(name, args.head.exptype -> Ti)
    SchemaApp(v, args.head)
  }
  def apply(v: SchemaConst, args: List[SchemaExpression]): SchemaExpression = {
    SchemaApp(v, args.head)
  }
  def unapply(s: SchemaExpression) = s match {
    case a: SchemaApp if a.arg.exptype == Ti && a.function.exptype == ->(Ti,Ti) => Some(a.function.asInstanceOf[SchemaExpression], a.arg.asInstanceOf[SchemaExpression])
    case _ => None
  }
}

// TODO: this seems to be hardcoded for a a single parameter
// plus 0 or 1 arguments. Generalize to simplify the code!
object sTerm {
  //the i should be of type Tindex !
  def apply(f: String, i: SchemaExpression, l: List[SchemaExpression]): SchemaExpression = {
    require(i.exptype == Tindex)
    if(l.isEmpty) {
      val func = SchemaConst(f, ->(Tindex , Ti))
      return SchemaApp(func, i)
    }
    else {
      val func = SchemaConst(f, ->(Tindex , ->(Ti, Ti)))
      return SchemaApp(SchemaApp(func, i), l.head)
    }
  }
  def apply(f: SchemaConst, i: SchemaExpression, l: List[SchemaExpression]): SchemaExpression = {
    require(i.exptype == Tindex)
    if(l.isEmpty) SchemaApp(f, i)
    else SchemaApp(SchemaApp(f, i), l.head)
  }

  def unapply(s : SchemaExpression) = s match {
    case SchemaApp(SchemaApp(func : SchemaConst, i), arg) if i.exptype == Tindex => Some( ( func, i, arg::Nil ) )
    case SchemaApp(func : SchemaConst, i) if i.exptype == Tindex => Some( ( func, i, Nil ) )
    case _ => None
  }
}

//indexed s-term of type ω->ω
object sIndTerm {
  //the i should be of type Tindex !
  def apply(f: String, i: IntegerTerm): SchemaExpression = {
    val func = SchemaConst(f, ->(Tindex , Tindex))
    return SchemaApp(func, i)
  }
  def unapply(s : SchemaExpression) = s match {
    case SchemaApp(func : SchemaConst, i) if i.exptype == Tindex => Some( ( func, i) )
    case _ => None
  }
}


//database for trs
object dbTRS extends Iterable[(SchemaConst, ((SchemaExpression, SchemaExpression), (SchemaExpression, SchemaExpression)))] {
  val map = new scala.collection.mutable.HashMap[SchemaConst, ((SchemaExpression, SchemaExpression), (SchemaExpression, SchemaExpression))]
  def get(name: SchemaConst) = map(name)
  def getOption(name: SchemaConst) = map.get(name)
  def clear = map.clear
  def add(name: SchemaConst, base: (SchemaExpression, SchemaExpression), step: (SchemaExpression, SchemaExpression)): Unit = {
    map.put(name, (base, step))
  }
  def iterator = map.iterator
}


class sTermRewriteSys(val func: SchemaConst, val base: SchemaExpression, val rec: SchemaExpression)
object sTermRewriteSys {
  def apply(f: SchemaConst, base: SchemaExpression, step: SchemaExpression) = new sTermRewriteSys(f, base, step)
}

object sTermDB extends Iterable[(SchemaConst, sTermRewriteSys)] with TraversableOnce[(SchemaConst, sTermRewriteSys)] {
  val terms = new scala.collection.mutable.HashMap[SchemaConst, sTermRewriteSys]
  def clear = terms.clear
  def get(func: SchemaConst) = terms(func)
  def put(sterm: sTermRewriteSys) = terms.put(sterm.func, sterm)
  def iterator = terms.iterator
}


// This factory creates a formula that
// is true iff param = 0
object isZero {
  def apply(param: IntegerTerm) =
    BigAnd( IntVar("i"), BottomC, Succ(IntZero()), param )
}

// This factory creates a formula that
// is true iff x > y
object isBiggerThan {
  def apply(x: IntegerTerm, y: IntegerTerm) =
    BigAnd( IntVar("i"), BottomC, x, y )
}

/*********************** Factories *****************************/

object SchemaFactory extends FactoryA {
  def createVar( name: String, exptype: TA) : SchemaVar = SchemaVar(name, exptype)
  def createConst(name: String, exptype: TA) : SchemaConst = SchemaConst(name, exptype)
  def createAbs( variable: Var, exp: LambdaExpression ): SchemaAbs = SchemaAbs( variable.asInstanceOf[IntVar], exp.asInstanceOf[SchemaExpression] )

  def createApp( fun: LambdaExpression, arg: LambdaExpression ): SchemaApp = SchemaApp(fun.asInstanceOf[SchemaExpression], arg.asInstanceOf[SchemaExpression])
}


//this substitution works for IntVar Only. It gives an instance of a schema.
/* All substitutions should die
class SchemaSubstitution[T <: HOLExpression](map: Map[Var, T]) extends Substitution[T](map) {
   override def applyWithChangeDBIndices(expression: T, protectedVars: List[Var]): T = expression match {
      case x:IntVar if !(protectedVars.contains(x)) => {
          map.get(x) match {
            case Some(t) => {
              //println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case None => {
              //println(x + " is free, but we don't substitute for it")
              x.asInstanceOf[T]
            }
        }
      }
      case x:IntVar => {
        if (map.contains( x ) )
          println("WARNING: trying to substitute for a bound variable, ignoring!")
       expression
      }
      case App(m,n) => App(applyWithChangeDBIndices(m.asInstanceOf[T], protectedVars), applyWithChangeDBIndices(n.asInstanceOf[T], protectedVars)).asInstanceOf[T]
      case abs: Abs => Abs(abs.variable, applyWithChangeDBIndices(abs.expressionInScope.asInstanceOf[T], abs.variable::protectedVars)).asInstanceOf[T]
      case _ => expression
  }
}
*/

/* All substitutions should die
class SchemaSubstitution1[T <: HOLExpression](val map: Map[Var, T])  {
  def apply(expression: T): T =  {
//    println("sub1, expression = "+expression)
    expression match {
      case x:IntVar => {
        //      println("\nIntVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[T]
          }
        }
      }
      case iov:indexedOmegaVar => {
        indexedOmegaVar(iov.name, apply(iov.index.asInstanceOf[T])).asInstanceOf[T]
      }
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case at @ Atom(name, args) => {
//        println("\nAtom begin")
        val atom = Atom(name, args.map(x => apply(x.asInstanceOf[T]).asInstanceOf[HOLExpression])).asInstanceOf[T]
//        println("Atom end\n")
        atom
      }
      case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case st @ sTerm(name, i, args) => {
//        println("\nsTerm")
        sTerm(name.asInstanceOf[HOLConst], apply(i.asInstanceOf[T]), args.map(x => apply(x.asInstanceOf[T]))).asInstanceOf[T]
      }
      case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLConst], apply(arg.asInstanceOf[T])::Nil).asInstanceOf[T]
      case _ => {
        //      println("\n SchemaSubstitution1: case _ => " + expression.toString + " : "+expression.getClass)
        expression
      }
    }
  }
}
*/

/* All substitutions should die
class SchemaSubstitution2[T <: HOLExpression](val map: Map[Var, T])  {
  def apply(expression: T): T = {
//    println("subst")
    expression match {
      case x:IntVar => {
        //      println("\nIntVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[T]
          }
        }
      }
      case x:foVar => {
//        println("\nfoVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[T]
          }
        }
      }
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case at @ Atom(name, args) => {
        Atom(name, args.map(x => apply(x.asInstanceOf[T]).asInstanceOf[HOLExpression])).asInstanceOf[T]
      }
      case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case st @ sTerm(name, i, args) => {
        sTerm(name.asInstanceOf[HOLConst], apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(args.asInstanceOf[T])::Nil).asInstanceOf[T]
      }
      case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLConst], apply(arg.asInstanceOf[T])::Nil).asInstanceOf[T]
      case sIndTerm(func, i) => {
        sIndTerm(func.toString, apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      }
      case _ => {
        //      println("\ncase _ =>")
        //      println(expression)
        expression
      }
    }
  }
}
*/


/* All substitutions should die
class SchemaSubstitutionCNF(val map: Map[Var, HOLExpression])  {
  def apply(expression: HOLExpression): HOLExpression = {
    //    println("subst")
    expression match {
      case x:IntVar => {
        //      println("\nIntVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[HOLExpression]
          }
        }
      }
      case x:foVar => {
        //        println("\nfoVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[HOLExpression]
          }
        }
      }
      case v: indexedOmegaVar => indexedOmegaVar(v.name, apply(v.index))
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[HOLExpression]).asInstanceOf[IntegerTerm]).asInstanceOf[HOLExpression]
      case Succ(n) => Succ(apply(n.asInstanceOf[HOLExpression]).asInstanceOf[IntegerTerm]).asInstanceOf[HOLExpression]
      case at.logic.language.hol.Or(l @ left, r @ right) => at.logic.language.hol.Or(apply(l.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
      case at.logic.language.hol.And(l @ left, r @ right) => at.logic.language.hol.And(apply(l.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
      case at.logic.language.hol.Neg(l @ left) => at.logic.language.hol.Neg(apply(l.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]).asInstanceOf[HOLExpression]
      case at.logic.language.hol.Atom(name, args) => {
        at.logic.language.hol.Atom(name, args.map(x => apply(x.asInstanceOf[HOLExpression]))).asInstanceOf[HOLExpression]
      }
      case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[HOLExpression]).asInstanceOf[IntegerTerm]).asInstanceOf[HOLExpression]
      case st @ sTerm(name, i, args) => {
//        println("\n st = "+st)
        sTerm(name, apply(i), apply(args.head)::Nil)
      }
      case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLConst], apply(arg.asInstanceOf[HOLExpression])::Nil).asInstanceOf[HOLExpression]
      case sIndTerm(func, i) => {
        sIndTerm(func.toString, apply(i).asInstanceOf[IntegerTerm])
      }
      case App(App(f,t1),t2) => {
//        println("\nAppN: " + expression)
        val rez = AppN(f, apply(t1.asInstanceOf[HOLFormula])::apply(t2.asInstanceOf[HOLFormula])::Nil).asInstanceOf[HOLExpression]
//        println("\nsub AppN: " + rez)
        rez
      }
      case _ => {
//        println("\ncase _ =>")
//        println(expression)
        expression
      }
    }
  }
}
*/

