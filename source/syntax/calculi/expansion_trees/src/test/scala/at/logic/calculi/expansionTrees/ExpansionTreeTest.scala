
package at.logic.calculi.expansionTrees

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.language.lambda.types.{Ti => i}


@RunWith(classOf[JUnitRunner])
class ExpansionTreeTest extends SpecificationWithJUnit {

  val alpha = HOLVar(("\\alpha" ), i)
  val beta = HOLVar(("\\beta" ), i)
  val c = HOLConst(("c" ), i)
  val d = HOLConst(("d" ), i)
  val f = HOLConst("f", i)
  val x = HOLVar(("x" ), i)
  val y = HOLVar(("y" ), i)
  val z = HOLVar(("z" ), i)
  val eq = HOLConst("=", i)
  val P = HOLConst("P", i)
  val Q = HOLConst("Q", i)

  val et1 = WeakQuantifier(
    ExVar(x, AtomHOL(eq, x::x::Nil)),
    List((Atom( AtomHOL(eq, c::c::Nil) ) , c))
  )

  val et2 = WeakQuantifier(
    ExVar(x, AtomHOL(P, x::y::c::Nil)),
    List((Atom( AtomHOL(P, z::y::c::Nil) ), z))
  )

  val et3 = StrongQuantifier(
    AllVar(x, AtomHOL(P, x::d::z::Nil)),
    z,
    Atom( AtomHOL(P, z::d::z::Nil) )
  )

  val et4 = WeakQuantifier(
    ExVar(x, AtomHOL(P, x::c::Nil)),
    List(
      (Atom( AtomHOL(P, z::c::Nil) ), z),
      (Atom( AtomHOL(P, y::c::Nil) ), y)
    )
  )

  "Expansion Trees substitution" should {

    "replace variables correctly 1" in {
      val s = Substitution(y, d)
      val etPrime = substitute(s, et2)

      etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x :: d :: c :: Nil)),
        List((Atom(AtomHOL(P, z :: d :: c :: Nil)), z))
      )
    }

    "replace variables correctly 2" in {
      val s = Substitution(z, d)
      val etPrime = substitute(s, et2)

      etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x :: y :: c :: Nil)),
        List((Atom(AtomHOL(P, d :: y :: c :: Nil)), d))
      )
    }

    "replace variables correctly 3" in {
      val s = Substitution(z, y)
      val etPrime = substitute(s, et3)

      etPrime mustEqual StrongQuantifier(
        AllVar(x, AtomHOL(P, x::d::y::Nil)),
        y,
        Atom( AtomHOL(P, y::d::y::Nil) )
      )
    }

    "not replace const " in {
      val s = Substitution(HOLVar("c", i), HOLConst("d", i))
      val etPrime = substitute(s, et1)

      etPrime mustEqual et1
    }

    "create merge node in case of collapse in weak quantifier instances " in {
      val s = Substitution(z, y)
      val etPrime = substitute.applyNoMerge(s, et4)

        etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x::c::Nil)),
        List(
          (MergeNode(Atom(AtomHOL(P, y::c::Nil)), Atom(AtomHOL(P, y::c::Nil))), y)
        )
      )
    }
  }

  "Expansion Trees merge" should {
    "merge identical trees" in {
      merge(MergeNode(et4, et4)) mustEqual( et4 )
    }

    "do simple substitution as result of merge" in {
      val etSubst1 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) ) )
      val etSubst2 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) ) )

      // from a theoretical point of view, the result could also be equal to the second tree, but users probably expect the algo to work from left to right
      merge( MergeNode(etSubst1, etSubst2) ) mustEqual etSubst1
    }

    "do simple substitution as result of merge with context" in {
      val etSubst1 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) ) )
      val etSubst2 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) ) )
      merge( MergeNode(etSubst1, etSubst2) ) mustEqual etSubst1
    }

    "do merge with substitution in other tree of sequent triggered by merge" in {
      // example from Chaudhuri et.al : A multi-focused proof system isomorphic to expansion proofs
      val etSubst1 = StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) )
      val etSubst2 = StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) )
      val fy = Function(f, y::Nil)
      val fz = Function(f, z::Nil)
      val seq = (Nil,
        // only succedent:
        MergeNode(etSubst1, etSubst2) ::
        WeakQuantifier(ExVar(x, AtomHOL(Q, x::Nil)), List(
          (Atom(AtomHOL(Q, fz::Nil)), fz ),
          (Atom(AtomHOL(Q, fy::Nil)), fy )
        )) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Atom( AtomHOL(P, y::Nil) ) ::
        Nil
        )
      val mergedSeq = merge(seq)

      // merge will trigger a substitution y -> z

      val testResult = new ExpansionSequent(Nil,
        (StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil)), z, Atom( AtomHOL(P, z::Nil))) ::
        WeakQuantifier(ExVar(x, AtomHOL(Q, x::Nil)), List( (Atom(AtomHOL(Q, fz::Nil)), fz))) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Nil).asInstanceOf[Seq[ExpansionTree]]
      )

      mergedSeq mustEqual testResult
    }



  }

}


