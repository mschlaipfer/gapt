/*
 * HOLExpressionArithmeticalExporter.scala
 *
 */

package at.logic.parsing.language.arithmetic

import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.schema.{TopC, BottomC, BigAnd, BigOr, SchemaFormula}
import at.logic.language.schema.logicSymbols.BiggerThanSymbol
import at.logic.parsing.OutputExporter
import at.logic.parsing.language.HOLTermExporter

trait HOLTermArithmeticalExporter extends OutputExporter with HOLTermExporter {
  def exportFunction(t: HOLExpression): Unit = t match {
    case TopC => getOutput.write("\\top")
    case BottomC => getOutput.write("\\bot")
    case Function(HOLConst("+",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" + "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("-",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" - "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("*",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" * "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("""/""",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(""" / """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst("<",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" < """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst(">",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst("=",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case BigAnd(v, f, s, e) =>
      getOutput.write("(")
      getOutput.write("""\bigwedge_{""")
      exportTerm(v)
      getOutput.write(" = ")
      exportTerm(s)
      getOutput.write("}^{")
      exportTerm(e)
      getOutput.write("}")
      exportTerm(f)
      getOutput.write(")")

    case BigOr(v, f, s, e) =>
      getOutput.write("(")
      getOutput.write("""\bigvee_{""")
      exportTerm(v)
      getOutput.write(" = ")
      exportTerm(s)
      getOutput.write("}^{")
      exportTerm(e)
      getOutput.write("}")
      exportTerm(f)
      getOutput.write(")")

    case Function(name, args, _) =>
      getOutput.write(name.toString)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")

    case Atom(sym, args) =>
      getOutput.write(sym.toString)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
  }
}
