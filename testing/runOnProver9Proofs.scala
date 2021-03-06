import java.io.{File, FileWriter}

import at.logic.gapt.proofs.lkOld.base.LKRuleCreationException
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.utils.withTimeout

object runOnProver9Proofs {
  /** The base prover9 path.
   *
   */
  val basePath = "testing/TSTP/prover9/"

  /** Where log files will be stored.
   *
   */
  val logDirPath = "testing/logs"

  /** The maximum time (in seconds) a test is allowed to take.
   *
   */
  val timeOut = 60

  /** Returns a list of files, sorted by file size in ascending order.
   *
   * @param path The path (relative to basePath) to search for files. Defaults to "", i.e. if called with no argument, all files in the prover9 directory will be returned.
   * @return A list of files.
   */
  def getFileList(path: String = "") = getFileListRec(basePath + path) sortBy {
    p => new File(p).length()
  }

  /** The recursive function that actually performs the file search.
   *
   * @param path The path to search for files.
   * @return List of files below path.
   */
  private def getFileListRec(path: String): List[String]  = {
    val file = new File(path)
    if (file.isDirectory) {
      val children = file.listFiles
      (children map (_.getPath) flatMap getFileListRec).toList
    }
    else if (file.getName.endsWith(".s.out"))
      List(file.getPath)
    else
      Nil
  }

  /** Applies a test function to all files below a given path.
    *
    * Curried so that you can write something like
    * {{{val test = runOnProver9Proofs(someFunction)
    * test("ALG")}}}
   *
   * @param f The test to be performed.
   * @param path The path below which the test should be performed, relative to basePath. Defaults to "", i.e. all files below basePath will be tested.
   */
  def apply(f: (String) => Unit)(path: String = ""): Unit = {
    val files = getFileList(path)

    val logDir = new File(logDirPath)

    // Clean up existing log files
    if (logDir.exists()) {
      val logs = logDir.listFiles()
      logs.foreach {_.delete()}
      logDir.delete()
    }


    // Perform the test on each file
    files.foreach {f}
  }

  /** Tests whether Prover9 import works.
   *
   * @param path The path of the proof to be imported.
   */
  def testImport(path: String): Unit = {

    // Name of the current subdirectory, i.e. ALG, ANA, etc
    val currentDir =  {
      val tmp = new File(path)
      tmp.getParentFile.getParentFile.getName
    }

    val logDir = new File(logDirPath)

    if (!logDir.exists())
      logDir.mkdir()

    // Try importing the given file for at most timeOut seconds
    try {
      withTimeout(1000 * timeOut)
      {Prover9Importer.lkProofFromFile(path)}
    }

    // The catch block is the interesting part of this function. My use case was to log only LKRuleCreationExceptions and disregard all others.
    catch {
      case e: LKRuleCreationException =>
        private val nLine = sys.props( "line.separator" )
        val logFileName = logDirPath + currentDir + ".txt"
        val writer = new FileWriter(logFileName, true)
        writer.append(path+ nLine )
        writer.append(e.toString+ nLine + nLine )
        writer.close()

      case _: Throwable =>
    }
  }
}
