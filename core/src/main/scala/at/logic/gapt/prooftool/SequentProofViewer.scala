package at.logic.gapt.prooftool

import java.io.{ ByteArrayInputStream, File, InputStreamReader, BufferedWriter => JBufferedWriter, FileWriter => JFileWriter }

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.formats.latex.{ ProofToLatexExporter, SequentsListLatexExporter }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof }
import at.logic.gapt.proofs.lksk.LKskProof
import at.logic.gapt.proofs.lksk.LKskProof.LabelledFormula
import at.logic.gapt.formats.latex.LatexUIRenderer.{ formulaToLatexString, labelledFormulaToLatexString }
import at.logic.gapt.formats.llk.exportLLK

import scala.swing._

/**
 * A ProofToolViewer for dag proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam T The type of dag proof..
 */
abstract class DagProofViewer[T <: DagProof[T]]( name: String, proof: DagProof[T] ) extends ProofToolViewer[DagProof[T]]( name, proof ) {
  override val content = proof

}

/**
 * A ProofToolViewer for sequent proofs. Used for LKsk and RAL proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 * @tparam F
 * @tparam T The type of sequent proof.
 */
class SequentProofViewer[F, T <: SequentProof[F, T]]( name: String, proof: SequentProof[F, T], sequent_element_renderer: F => String ) extends DagProofViewer[T]( name, proof ) {
  override type MainComponentType = DrawSequentProof[F, T]
  override def createMainComponent( fSize: Int ) = new DrawSequentProof(
    this,
    proof,
    fSize,
    hideContexts = false,
    Set(),
    markCutAncestors = false,
    Set(),
    "",
    sequent_element_renderer
  )

  def hideSequentContext() {
    mainComponent.hideContexts = true
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def showAllFormulas() {
    mainComponent.hideContexts = false
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  /**
   * Displays the dag proof in sunburst form.
   */
  def sunburstView() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    initSunburstDialog( name, content )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def initSunburstDialog( name: String, proof: DagProof[T] ) {
    val d = new SunburstTreeDialog( this, name, proof, sequent_element_renderer )
    d.pack()
    d.centerOnScreen()
    d.open()
  }

  /*def displaySunburst( name: String, proof: DagProof[T] ) {
    showFrame()
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    proof match { case proof: SequentProof[_, _] => loadProof( ( name, proof ) ) }
    initSunburstDialog( name, proof )
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }*/

}

/**
 * A ProofToolViewer for LK proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 */
class LKProofViewer( name: String, proof: LKProof ) extends SequentProofViewer[HOLFormula, LKProof]( name, proof, formulaToLatexString ) with Savable[LKProof] with ContainsLKProof {
  override val content: LKProof = proof
  override def fileMenuContents = Seq( openButton, saveAsButton, new Separator, exportToPDFButton, exportToPNGButton )
  override def viewMenuContents = super.viewMenuContents ++ Seq( new Separator(), hideStructuralRulesButton, hideContextsButton, markCutAncestorsButton, new Separator(), viewExpansionProofButton, sunburstViewButton )

  /**
   * Displays the expansion proof of proof in a new window.
   */
  def expansionTree() {
    try {
      scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
      prooftool( LKToExpansionProof( content ), "Expansion tree" )
      scrollPane.cursor = java.awt.Cursor.getDefaultCursor
    } catch {
      case e: Throwable =>
        errorMessage( "Cannot extract expansion tree." + dnLine + getExceptionString( e ) )
    } finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }

  }

  override def fSave( name: String, proof: LKProof ) {
    chooser.fileFilter = chooser.acceptAllFileFilter
    chooser.showSaveDialog( mBar ) match {
      case FileChooser.Result.Approve =>
        scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
        val result = chooser.selectedFile.getPath
        // val pair = body.getContent.getData.get
        try {
          if ( result.endsWith( ".llk" ) || chooser.fileFilter.getDescription == ".llk" ) {
            val filename = if ( result.endsWith( ".llk" ) ) result else result + ".llk"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( exportLLK( proof ) )
            file.close()
          } else if ( result.endsWith( ".tex" ) || chooser.fileFilter.getDescription == ".tex" ) {
            val filename = if ( result.endsWith( ".tex" ) ) result else result + ".tex"
            val file = new JBufferedWriter( new JFileWriter( filename ) )
            file.write( ProofToLatexExporter( proof ) )
            file.close()
          } else infoMessage( "Proofs cannot be saved in this format." )
        } catch { case e: Throwable => errorMessage( "Cannot save the proof! " + dnLine + getExceptionString( e ) ) }
        finally { scrollPane.cursor = java.awt.Cursor.getDefaultCursor }
      case _ =>
    }
  }

  def hideStructuralRules(): Unit = publisher.publish( HideStructuralRules )
  def showAllRules(): Unit = publisher.publish( ShowAllRules( content ) )

  def markCutAncestors() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    mainComponent.markCutAncestors = true
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def removeMarking(): Unit = {
    mainComponent.markCutAncestors = false
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // New menu buttons
  def saveAsButton = MenuButtons.saveAsButton[LKProof]( this.asInstanceOf[ProofToolViewer[LKProof] with Savable[LKProof]] )

  def hideStructuralRulesButton = MenuButtons.hideStructuralRulesButton( this )

  def hideContextsButton = MenuButtons.hideContextsButton( this )

  def markCutAncestorsButton = MenuButtons.marCutAncestorsButton( this )

  def viewExpansionProofButton = new MenuItem( Action( "View expansion proof" ) {
    expansionTree()
  } )

  def sunburstViewButton = new MenuItem( Action( "Sunburst View" ) {
    sunburstView()
  } )
}

/**
 * A ProofToolViewer for LK proofs.
 *
 * @param name The name to be displayed at the top.
 * @param proof The proof to be displayed.
 */
class LKskProofViewer( name: String, proof: LKskProof ) extends SequentProofViewer[LabelledFormula, LKskProof]( name, proof, labelledFormulaToLatexString ) {
  override val content: LKskProof = proof
  override def fileMenuContents = Seq( openButton, new Separator, exportToPDFButton, exportToPNGButton )
  override def viewMenuContents = super.viewMenuContents ++ Seq( new Separator(), sunburstViewButton )

  def hideStructuralRules(): Unit = publisher.publish( HideStructuralRules )
  def showAllRules(): Unit = publisher.publish( ShowAllRules( content ) )

  def markCutAncestors() {
    scrollPane.cursor = new java.awt.Cursor( java.awt.Cursor.WAIT_CURSOR )
    mainComponent.markCutAncestors = true
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  def removeMarking(): Unit = {
    mainComponent.markCutAncestors = false
    mainComponent.initialize()
    mainComponent.revalidate()
    scrollPane.cursor = java.awt.Cursor.getDefaultCursor
  }

  // New menu buttons
  //  def saveAsButton = MenuButtons.saveAsButton[LKProof]( this.asInstanceOf[ProofToolViewer[LKProof] with Savable[LKProof]] )

  //  def hideStructuralRulesButton = MenuButtons.hideStructuralRulesButton( this )

  //  def hideContextsButton = MenuButtons.hideContextsButton( this )

  //  def markCutAncestorsButton = MenuButtons.marCutAncestorsButton( this )

  def sunburstViewButton = new MenuItem( Action( "Sunburst View" ) {
    sunburstView()
  } )
}