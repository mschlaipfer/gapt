/*
 * Symbols.scala
 */

package at.logic.language.lambda.symbols

abstract class SymbolA

// This is used for renaming variables during substitution.
// DO NOT confuse this with DeBruijn indices, there are no such indices in
// this program.
class VariantSymbol(val s: String, val i: Int) extends SymbolA {
  override def toString() = s + i
}
object VariantSymbol {
  def apply(s: String) : VariantSymbol = new VariantSymbol(s, 0)
  def apply(s: String, i: Int) : VariantSymbol = new VariantSymbol(s, i)
  def unapply(sym: SymbolA) = sym match {
    case vs : VariantSymbol => Some((vs.s, vs.i))
    case _ => None
  }
}

class StringSymbol(val s: String) extends SymbolA {
  override def toString() = s
}
object StringSymbol {
  def apply(s: String) = new StringSymbol(s)
  def unapply(s: SymbolA) = s match {
    case ss : StringSymbol => Some(ss.s)
    case _ => None
  }
}

// TODO: implement
// Renames the variables in 'toRename' such that the new names do not clash
// with variables in 'blackList'.
// Note: to rename one variable v, call getRenaming(List(v), List()). Create a
// new method with that??
// TODO: Var is not visible here... find another place for this.
//object getRenaming {
//  def apply(toRename: List[Var], blackList: List[Var]) = toRename
//}

