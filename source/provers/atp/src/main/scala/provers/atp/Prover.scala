/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol._
import at.logic.parsing.calculi.ResolutionParser
import at.logic.algorithms.subsumption.{StillmanSubsumptionAlgorithm, SubsumptionAlgorithm} // to enable configuration
import refinements._
import commands._
import commandsParsers._
import ui.UserInterface

import java.util.Calendar

/**
 * A generic prover for resolution calculus. Not thread safe!
 */
object Prover {
    def main(args: Array[String]) {
      val prover = new Prover{}
      
      ()
    }
  }

trait Prover {
  /**
   * Refutes input clauses if possible
   * @param clausesInput the input clauses
   * @return a stream that instantiate all possible refutations
   */
  def refute(commands: Stream[Command]) : Stream[ResolutionProof] = {
    startingTime = (Calendar.getInstance().getTimeInMillis / 1000)
    // here we have the commands that are before the refutation process
    // such as loading the commands parser and refinement
    
    refute(commands, EmptyCom)
  }

  private def refute(commands: Stream[Command], lastCommand: Command): Stream[ResolutionProof] =
    refuteOne(commands, lastCommand) match {
      case (None, _) => Stream.empty
      case (Some(p), (comms, compocom)) => Stream.cons(p, refute(comms, compocom))
    }

  private def refuteOne(commands: Stream[Command], last: Command) : Tuple2[Option[ResolutionProof],Tuple2[Stream[Command],Command]] =
    refuteOne1Step(last, commands.head) match {
      case CorrectResolventFound(res) => (Some(res),(commands.tail,CorrectResolventFound(res)))
      case FailureCom => (None, (commands.tail, FailureCom))
      // if the command was to insert into command stream
      case AppendCommandsCom(coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), EmptyCom)
      case x => refuteOne(commands.tail, x)
    }

  private def refuteOne1Step(composedCommand: Command, newCommand: Command): Command = 
    if (timeLimit > 0 && (Calendar.getInstance().getTimeInMillis / 1000) - startingTime > timeLimit) FailureCom
    else
    (composedCommand, newCommand) match {
      case (EmptyCom, SetTimeLimit(n)) => timeLimit = n; EmptyCom
      case (EmptyCom, SetUICom(uinterface)) => userInterface = uinterface; EmptyCom
      case (EmptyCom, SetRefinementCom(ref)) => refinement = ref; EmptyCom
      case (EmptyCom, SetCommandsParserCom(comparse)) => commandsParser = comparse; EmptyCom
      case (EmptyCom, ErrorCom(msg)) if userInterface == null => FailureCom
      case (EmptyCom, ErrorCom(msg)) => userInterface.parse(ErrorCom(msg))
      // ensures that all settings were set
      case (EmptyCom, a) if (userInterface == null || refinement == null || commandsParser == null) =>
        AppendCommandsCom(ErrorCom("ui, refinement or commandsParser were not initialized")::a::Nil)
      // insert clauses to set
      case (EmptyCom, SetTargetResolventCom(tProof)) => targetProof = tProof; EmptyCom
      // deal with the case the input set already contains the target clause
      // therefore it returns the default empty clause as no refutation was made
      case (EmptyCom, GetClausesCom) if targetExistsIn(refinement.clauses) => CorrectResolventFound(targetProof)
      // try to obtain the required clauses, return fail command if not possible
      case (EmptyCom, GetClausesCom) => refinement.getNextClausesPair match {
        case None => FailureCom
        case Some(clauses) => GotClausesPairCom(clauses)
      }
      case (ResultedClauseCom(res), _) if (targetProof.root.formulaEquivalece(res.root)) => CorrectResolventFound(res)
      case (ResultedClauseCom(res), InsertCom) => refinement.insertProof(res); EmptyCom
      case (r@ ResultedClauseCom(res), IfNotTautologyCom) => if (!res.root.negative.exists(f => res.root.positive.contains(f))) r else NoResultedClauseCom()
      case (r@ ResultedClauseCom(res), IfNotForwardSubsumedCom(subsumpMng)) => if (!subsumpMng.forwardSubsumption(res.root)) r else NoResultedClauseCom()
      case (r@ ResultedClauseCom(res), BackwardSubsumptionCom(subsumpMng)) => {subsumpMng.backwardSubsumption(res.root); r}
      case (NoResultedClauseCom(), InsertCom) => EmptyCom
      case (NoResultedClauseCom(), IfNotTautologyCom) => NoResultedClauseCom()
      case (NoResultedClauseCom(), IfNotForwardSubsumedCom(_)) => NoResultedClauseCom()
      case (NoResultedClauseCom(), BackwardSubsumptionCom(_)) => NoResultedClauseCom()
      // logical commands
      case (com, AndCom(ls1, ls2)) => AppendCommandsCom((com::ls1):::(com::ls2))
      // pass parsing to customized commands parser
      case _ => commandsParser.parse(composedCommand, newCommand)
    }

  private def targetExistsIn(clauses: Iterable[Clause]) = clauses.exists(a => targetProof.root.formulaEquivalece(a))

  var targetProof: ResolutionProof = theEmptyClause() // override in commands if target is different
  var timeLimit: Long = -1
  var startingTime: Long = -1
  var refinement: Refinement = null
  var commandsParser: CommandsParser = null
  var userInterface: UserInterface = null
}
