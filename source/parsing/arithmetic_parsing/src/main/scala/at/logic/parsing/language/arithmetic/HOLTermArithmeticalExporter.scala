/*
 * HOLExpressionArithmeticalExporter.scala
 *
 */

package at.logic.parsing.language.arithmetic

import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.schema.{TopC, BottomC, BigAnd, BigOr, SchemaFormula}
import at.logic.language.schema.logicSymbols.BiggerThanSymbol
import at.logic.language.fol
import at.logic.parsing.OutputExporter
import at.logic.parsing.language.HOLTermExporter

trait HOLTermArithmeticalExporter extends OutputExporter with HOLTermExporter {
  def exportFunction(t: HOLExpression): Unit = t match {
    case TopC => getOutput.write("\\top")
    case BottomC => getOutput.write("\\bot")
<<<<<<< .working
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
=======
    case Function(ConstantStringSymbol("+"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" + "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("-"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" - "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("*"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" * "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("""/"""), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(""" / """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("<"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" < """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol(">"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(BiggerThanSymbol, x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("="), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case Equation(x,y) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case fol.Equation(x,y) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case BigAnd(v, f, s, e) => {
      getOutput.write("("); getOutput.write("""\bigwedge_{"""); exportTerm(v); 
                                getOutput.write(" = "); exportTerm(s) ; getOutput.write("}^{"); exportTerm(e);
                                getOutput.write("}"); exportTerm(f); getOutput.write(")")}
    // FIXME: SCALA BUG!
    case _ => t match {
    case BigOr(v, f, s, e) => {
      getOutput.write("("); getOutput.write("""\bigvee_{"""); exportTerm(v); 
                                getOutput.write(" = "); exportTerm(s) ; getOutput.write("}^{"); exportTerm(e);
                                getOutput.write("}"); exportTerm(f); getOutput.write(")")}
>>>>>>> .merge-right.r1940

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
<<<<<<< .working

=======
    }
>>>>>>> .merge-right.r1940
<<<<<<< .working
    case Atom(sym, args) =>
      getOutput.write(sym.toString)
      getOutput.write("(")
=======
    case Atom(sym, args) => {
      var nonschematic = sym match {
        case cs : ClauseSetSymbol => {
          getOutput.write("CL^{(");

          writeCutConf(cs.cut_occs);
          getOutput.write("),");
          getOutput.write(cs.name);
          getOutput.write("}_{");
          getOutput.write("{");
          false;
        }
        case _ =>
          getOutput.write(sym.toString)
          true
      }
      if(nonschematic) {
        getOutput.write("(")
        getOutput.write("{")
      }

>>>>>>> .merge-right.r1940
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
<<<<<<< .working
      getOutput.write(")")
=======

      if(nonschematic){
        getOutput.write(")}")
      }
      else
        getOutput.write("}}")
    }
>>>>>>> .merge-right.r1940
  }
<<<<<<< .working
=======
  }}

  def exportSymbol(sym: SymbolA): Unit = sym match {
    case cs : ClauseSetSymbol =>
      getOutput.write("CL^{("); writeCutConf(cs.cut_occs);
      getOutput.write("),");
      getOutput.write(cs.name);
      getOutput.write("}")
    case _ => getOutput.write(sym.toString)
  }

  private def writeCutConf( cc: CutConfiguration) = {
    if(cc._1.size > 0) {
      exportTerm( cc._1.head );
      cc._1.tail.foreach ( f => {getOutput.write(", "); exportTerm( f ) })
    }
    getOutput.write("|")
    if(cc._2.size > 0) {
      exportTerm( cc._2.head )
      cc._2.tail.foreach ( f => {getOutput.write(", "); exportTerm( f ) })
    }
  }
>>>>>>> .merge-right.r1940
}
