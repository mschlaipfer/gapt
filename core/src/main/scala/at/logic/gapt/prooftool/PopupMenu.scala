package at.logic.gapt.prooftool

import at.logic.gapt.proofs.{ SequentProof, DagProof }
import at.logic.gapt.proofs.lk.LKProof

import swing.SequentialContainer.Wrapper
import javax.swing.JPopupMenu
import swing._
import at.logic.gapt.expr._

class PopupMenu extends Component with Wrapper {
  override lazy val peer: JPopupMenu = new JPopupMenu

  def show( invoker: Component, x: Int, y: Int ) { peer.show( invoker.peer, x, y ) }
}

object PopupMenu {

  // PopupMenu for LKProofs.
  def apply[T <: DagProof[T]]( main: DagProofViewer[T], tproof: DagProof[T], component: Component, x: Int, y: Int ) {
    lazy val proof = tproof.asInstanceOf[LKProof]
    val popupMenu = new PopupMenu {
      contents += new Separator
      //      contents += new MenuItem( Action( "Apply Gentzen's Method (new)" ) { Main.newgentzen( proof ) } )
      //      contents += new MenuItem( Action( "Apply Gentzen's Method" ) { Main.gentzen( proof ) } )
      contents += new Separator
      contents += new MenuItem( Action( "Save Subproof as..." ) { /*main.fSave( ( proof.name, proof ) )*/ } )
      contents += new Separator
      contents += new MenuItem( Action( "Show Proof Above" ) { main.publisher.publish( ShowProof( tproof ) ) } )
      contents += new MenuItem( Action( "Hide Proof Above" ) { main.publisher.publish( HideProof( tproof ) ) } )
      contents += new Separator
    }
    popupMenu.show( component, x, y )
  }

  def apply[F, T <: SequentProof[F, T]]( main: SequentProofViewer[F, T], tproof: SequentProof[F, T], component: Component, x: Int, y: Int ) {
    lazy val proof = tproof.asInstanceOf[LKProof]
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "View Subproof as Sunburst Tree" ) {
        main.initSunburstDialog( "subproof " + proof.name, tproof )
      } )
      contents += new Separator
      //      contents += new MenuItem( Action( "Apply Gentzen's Method (new)" ) { Main.newgentzen( proof ) } )
      //      contents += new MenuItem( Action( "Apply Gentzen's Method" ) { Main.gentzen( proof ) } )
      contents += new Separator
      contents += new MenuItem( Action( "Save Subproof as..." ) { /*main.fSave( ( proof.name, proof ) )*/ } )
      contents += new Separator
      contents += new MenuItem( Action( "Show Proof Above" ) { main.publisher.publish( ShowProof( tproof ) ) } )
      contents += new MenuItem( Action( "Hide Proof Above" ) { main.publisher.publish( HideProof( tproof ) ) } )
      contents += new Separator
    }
    popupMenu.show( component, x, y )
  }

  // PopupMenu for Expansion Trees.
  def apply( det: DrawExpansionTree, f: HOLFormula, component: Component, x: Int, y: Int ) {
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "Close" ) { det.close( f ) } )
      contents += new MenuItem( Action( "Open" ) { det.open( f ) } )
      contents += new MenuItem( Action( "Expand" ) { det.expand( f ) } )
    }
    popupMenu.show( component, x, y )
  }

  // PopupMenu for the title label of either cedent
  def apply( main: ExpansionSequentViewer, ced: CedentPanel, x: Int, y: Int ) {
    val popupMenu = new PopupMenu {
      val trees = ced.treeList.drawnTrees
      contents += new MenuItem( Action( "Close all" ) { trees.foreach( det => det.close( det.expansionTree.shallow ) ) } )
      contents += new MenuItem( Action( "Open all" ) {
        for ( det <- trees ) {
          val subFs = firstQuantifiers( det.expansionTree.shallow )
          subFs.foreach( det.open )
        }
      } )

      contents += new MenuItem( Action( "Expand all" ) { trees.foreach( det => expandRecursive( det, det.expansionTree.shallow ) ) } )
      contents += new MenuItem( Action( "Reset" ) {
        ced.treeList = new TreeListPanel( main, ced.cedent, ced.ft )
        ced.scrollPane.contents = ced.treeList
        ced.revalidate()
      } )
    }
    popupMenu.show( ced.titleLabel, x, y )
  }

  def firstQuantifiers( f: HOLFormula ): List[HOLFormula] = f match {
    case HOLAtom( _, _ )          => Nil
    case And( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Imp( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Or( l, r )               => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Neg( l )                 => firstQuantifiers( l )
    case All( _, _ ) | Ex( _, _ ) => List( f )
  }

  def expandRecursive( det: DrawExpansionTree, f: HOLFormula ): Unit = f match {
    case HOLAtom( _, _ ) =>
    case And( l, r ) =>
      expandRecursive( det, l ); expandRecursive( det, r )
    case Imp( l, r ) =>
      expandRecursive( det, l ); expandRecursive( det, r )
    case Or( l, r ) =>
      expandRecursive( det, l ); expandRecursive( det, r )
    case Neg( l ) => expandRecursive( det, l )
    case All( _, l ) =>
      det.expand( f ); expandRecursive( det, l )
    case Ex( _, l ) => det.expand( f ); expandRecursive( det, l )
  }
}

