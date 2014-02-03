/*
 * HOLExpressionExporter.scala
 *
 */

package at.logic.parsing.language.xml

import at.logic.language.hol._
import at.logic.parsing.ExportingException
import at.logic.language.lambda.types.Ti
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.To

trait HOLTermExporter {
  def exportTerm(term: HOLExpression): scala.xml.Elem = term match {
    case Atom(name: HOLConst, args) =>
      <constantatomformula symbol={name.toString}>
        {exportList(args)}
      </constantatomformula>
    case Atom(name: HOLVar, args) =>
      <variableatomformula>
        {exportList(name::args)}
      </variableatomformula>
    // TODO Function with HOLVar
    case Function(f: HOLConst, args, _) =>
      <function symbol={f.toString}>
        {exportList(args)}
      </function>
    case And(left,right) =>
      <conjunctiveformula type="and">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Or(left,right) =>
      <conjunctiveformula type="or">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Imp(left,right) =>
      <conjunctiveformula type="impl">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Neg(f) =>
      <conjunctiveformula type="neg">
        {exportTerm(f)}
      </conjunctiveformula>
    case _ => exportTerm2(term)
  }
  private def exportTerm2(term: HOLExpression): scala.xml.Elem = term match {
    case AllVar(vr@HOLVar(_,Ti),f) =>
      <quantifiedformula type="all">
        {exportList(vr::f::Nil)}
      </quantifiedformula>
    case ExVar(vr@HOLVar(_,Ti),f) =>
      <quantifiedformula type="exists">
        {exportList(vr::f::Nil)}
      </quantifiedformula>
    case AllVar(vr@HOLVar(_,->(Ti,To)),f) =>
      <secondorderquantifiedformula type="all">
        {exportList(vr::f::Nil)}
      </secondorderquantifiedformula>
    case ExVar(vr@HOLVar(_,->(Ti,To)),f) =>
      <secondorderquantifiedformula type="exists">
        {exportList(vr::f::Nil)}
      </secondorderquantifiedformula>
    case _ => exportTerm3(term)
  }
  private def exportTerm3(term: HOLExpression): scala.xml.Elem = term match {
    // TODO: variables and constants of other types
    case HOLVar(a, Ti) =>
      <variable symbol={a.toString}/>
    case HOLVar(a, ->(Ti, To)) =>
      <secondordervariable symbol={a.toString}/>
    case HOLConst(a, Ti) =>
      <constant symbol={a.toString}/>
    /*
    case AppN1(Var(ConstantStringSymbol(a),FunctionType(Ti(),_)),args) =>
      <function symbol={a}>
        {exportList(args)}
      </function>
    case Var(VariableStringSymbol(a), ->(Ti(),To())) =>
      <secondordervariable symbol={a}/>
    case AbsN1(varlist, func) =>
      <lambdasubstitution>
        <variablelist>
          {exportList(varlist)}
        </variablelist>{exportTerm(func.asInstanceOf[HOLExpression])}
      </lambdasubstitution>
    case AppN(Var(ConstantStringSymbol(a),FunctionType(To(),ls)),args) if (ls.last == Ti()) =>
      <definedset definition={a} symbol={a}>
        {exportList(args)}
      </definedset>
    */
    case _ => throw new ExportingException("Term cannot be exported into the required xml format: " + term.toString)
  }
  private def exportList(ls: List[HOLExpression]) = ls.map(x => exportTerm(x))
}
