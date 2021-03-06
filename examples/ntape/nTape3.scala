package at.logic.gapt.examples

import at.logic.gapt.formats.llk.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
object nTape3 extends nTape {

  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "ntape/ntape3.llk" )

  override def root_proof() = "TAPEPROOF"

}
