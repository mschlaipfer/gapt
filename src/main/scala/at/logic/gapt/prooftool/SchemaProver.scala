package at.logic.gapt.prooftool

import at.logic.gapt.formats.shlk_parsing.sFOParser
import at.logic.gapt.language.hol.HOLExpression
import at.logic.gapt.language.schema._
import at.logic.gapt.proofs.lk.algorithms.solve
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.shlk.{SchemaProofDB, SchemaProof}
import scala.swing.Dialog

/**
 * Created by mrukhaia on 12/15/14.
 */

object SchemaProver {
  def apply(): Unit = try {
    Main.body.cursor = new java.awt.Cursor(java.awt.Cursor.WAIT_CURSOR)
    val t = TextAreaDialog("Please enter a sequent schema:")
    if (t != None && t.get != "") {
      val s = parse(t.get)
      prove(s)
    }
  } finally {
    Main.body.cursor = java.awt.Cursor.getDefaultCursor
  }

  def parse(t: String): FSequent = try {
      val sequent = sFOParser.parseSequent(t)
      val defs = dbTRS.map.map(p => p._2._1::p._2._2::Nil).flatten.toMap[HOLExpression,HOLExpression]
      Main.db.addDefinitions(defs)
      ProofToolPublisher.publish(ProofDbChanged)
      sequent
    } catch {
      case e: Throwable =>
        throw new Exception("Cannot parse the sequent!\n\n" + Main.getExceptionString(e))
    }

  def prove(s: FSequent): Unit = {
    val k = IntVar("k")
    val sp = new SchemaProof("\\psi", k::Nil, s, null, null)
    SchemaProofDB.clear
    SchemaProofDB.put(sp)
    val subst_0 = SchemaSubstitution((k, IntZero()) :: Nil)
    val s_0 =  FSequent(s.antecedent.map(fo => subst_0(fo)),
      s.succedent.map(fo => subst_0(fo)))
    val subst_k = SchemaSubstitution((k, Succ(k)) :: Nil)
    val s_k = FSequent(s.antecedent.map(fo => subst_k(fo)),
      s.succedent.map(fo => subst_k(fo)))
    Main.db.addSeqList(List(s_0,s_k))

    try {
      val p_base = try {
        solve.solveSchema(sp.b_res)
      } catch {
        case e: Throwable => Main.errorMessage("Cannot prove the base case!\n\n" + Main.getExceptionString(e))
          throw new Exception("Terminating with None")
      }

      Main.db.addProofs(("\\psi_base", p_base.get) :: Nil)
      ProofToolPublisher.publish(ProofDbChanged)
      Main.updateLauncher("\\psi_base", p_base.get, 16)
      Main.questionMessage("Proof of the base case found.\r\nStart proving the step case") match {
        case Dialog.Result.Yes =>
          val p_step = try {
            solve.solveSchema(sp.r_res)
          } catch {
            case e: Throwable => Main.errorMessage("Cannot prove the step case!\n\n" + Main.getExceptionString(e))
              throw new Exception("Terminating with None")
          }
          Main.db.addProofs(("\\psi_step", p_step.get) :: Nil)
          Main.updateLauncher("\\psi_step", p_step.get, 16)
          ProofToolPublisher.publish(ProofDbChanged)
        case _ =>
      }
    } catch {
      case e: Throwable => println(e.getMessage)
    }
  }
}
