package at.logic.provers.atp.commands

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 15, 2010
 * Time: 3:10:14 PM
 * To change this template use File | Settings | File Templates.
 */

package sequents {
import _root_.at.logic.algorithms.subsumption.managers.{SimpleManager, SubsumptionManager}
import _root_.at.logic.algorithms.subsumption.SubsumptionAlgorithm
import _root_.at.logic.calculi.lk.base.Sequent
import _root_.at.logic.utils.ds.{PublishingBuffer}
import at.logic.provers.atp.commands.base.{ResultCommand, DataCommand}
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.provers.atp.Definitions._
import at.logic.calculi.lk.base.types._

  abstract class SetSequentsCommand[V <: Sequent](val clauses: Iterable[Sequent]) extends DataCommand[V]

  // set the target clause, i.e. the empty clause normally
  case class SetTargetClause[V <: Sequent](val clause: Sequent) extends DataCommand[V] {
    def apply(state: State, data: Any) = List((state += new Tuple2("targetClause", clause), data))
  }

  // tests whether the clauses list contains the target clause
  case class SearchForEmptyClauseCommand[V <: Sequent]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[Sequent]
      state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]].find(x => x.root setEquals target)
    }
  }

  case class InsertResolventCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]] += data.asInstanceOf[ResolutionProof[V]]
      List((state,data))
    }
  }

  // deterministically trying to match all indices (it is deterministic as it does not change the state of the different cases)
  case class ApplyOnAllPolarizedLiteralPairsCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      val p = data.asInstanceOf[Tuple2[ResolutionProof[V],ResolutionProof[V]]]
      (for (i <- p._1.root.antecedent; j <- p._2.root.succedent) yield (state, ((p._2,p._1), (j, i))))  ++
      (for (i <- p._1.root.succedent; j <- p._2.root.antecedent) yield (state, (p, (i,j))))
    }
  }

  case class RefutationReachedCommand[V <: Sequent]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[Sequent]
      val d = data.asInstanceOf[ResolutionProof[V]]
      if (d.root setEquals target) Some(d)
      else None
    }
  }

  case class IfNotExistCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      val buffer = state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
      val res = data.asInstanceOf[ResolutionProof[V]]
      if (!buffer.exists(x => x.root == res.root)) List((state,data)) else List()
    }
  }

  case class SimpleForwardSubsumptionCommand[V <: Sequent](alg: SubsumptionAlgorithm) extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      // create a manager if not existing
      val manager: SubsumptionManager = if (state.isDefinedAt("simpleSubsumManager")) state("simpleSubsumManager").asInstanceOf[SubsumptionManager]
        else {
        val buffer = state("clauses").asInstanceOf[PublishingBuffer[FSequent]]
        val man = new SimpleManager(buffer, alg)
        state("simpleSubsumManager") = man
        man
      }
      val res = data.asInstanceOf[Sequent]
      val res1 = res.toFSequent()
      if (manager.forwardSubsumption(res1)) List() else List((state,data))
    }
  }

  case class SimpleBackwardSubsumptionCommand[V <: Sequent](alg: SubsumptionAlgorithm) extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      // create a manager if not existing
      val manager: SubsumptionManager = if (state.isDefinedAt("simpleSubsumManager")) state("simpleSubsumManager").asInstanceOf[SubsumptionManager]
        else {
        val buffer = state("clauses").asInstanceOf[PublishingBuffer[FSequent]]
        val man = new SimpleManager(buffer, alg)
        state("simpleSubsumManager") = man
        man
      }
      val res = data.asInstanceOf[Sequent]
      val res1 = res.toFSequent()
      manager.backwardSubsumption(res1)
      List((state,data))
    }
  }
}
