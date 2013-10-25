
package at.logic.calculi.resolution

import at.logic.calculi.proofs._
import at.logic.language.fol._
import at.logic.utils.ds.acyclicGraphs._

// NOTE: AppliedSubstitution had FOLExpression type

case object InstanceType extends UnaryRuleTypeA

trait RobinsonProofWithInstance extends RobinsonResolutionProof

object Instance {
  def apply(p: RobinsonResolutionProof, sub: Substitution): RobinsonResolutionProof = {
    val newCl = Clause( createContext( p.root.antecedent, sub ), createContext( p.root.succedent, sub ) )
    new UnaryAGraph[Clause](newCl, p)
        with UnaryResolutionProof[Clause] with AppliedSubstitution with RobinsonProofWithInstance {
          def rule = InstanceType
          def substitution = sub
          override def toString = "Inst(" + root.toString + ", " + p.toString + ", " + substitution.toString + ")"
          override def name = "Instance"
          def getAccumulatedSubstitution = substitution compose p.getAccumulatedSubstitution
        }
  }

  def unapply(proof: ResolutionProof[Clause] with AppliedSubstitution) = if (proof.rule == InstanceType) {
      val pr = proof.asInstanceOf[UnaryResolutionProof[Clause] with AppliedSubstitution]
      Some((pr.root, pr.uProof.asInstanceOf[RobinsonResolutionProof], pr.substitution))
    }
    else None
}
