
package at.logic.algorithms.lk

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success

import at.logic.calculi.lk.base.FSequent
import at.logic.language.schema._
import at.logic.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class SolvePropositionalTest extends SpecificationWithJUnit {
  "SolvePropositionalTest" should {
    "solve the sequents" in {
      val k = IntVar("k")
      val real_n = IntVar("n")
      val n = k
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)

      val i = IntVar("i")
      val A = IndexedPredicate("A", i)
      val B = IndexedPredicate("B", i)
      val C = IndexedPredicate("C", i)
      val zero = IntZero(); 
      val one = Succ(IntZero()); 
      val two = Succ(Succ(IntZero())) 
      val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three)
      val five = Succ(four) 
      val six = Succ(Succ(four))
      val seven = Succ(Succ(five))
      val A0 = IndexedPredicate("A", IntZero())
      val A1 = IndexedPredicate("A", one)
      val A2 = IndexedPredicate("A", two)
      val A3 = IndexedPredicate("A", three)

      val B0 = IndexedPredicate("B", IntZero())

      val Ak = IndexedPredicate("A", k)
      val Ai = IndexedPredicate("A", i)
      val Ai1 = IndexedPredicate("A", Succ(i))
      val orneg = Or(Neg(Ai), Ai1)

      val Ak1 = IndexedPredicate("A", Succ(k))
      val An = IndexedPredicate("A", k)
      val An1 = IndexedPredicate("A", n1)
      val An2 = IndexedPredicate("A", n2)
      val An3 = IndexedPredicate("A", n3)

      val biga = BigAnd(i, A, zero, one)
      val bigo = BigOr(i, A, zero, one)
      val biga2 = BigAnd(i, A, zero, two)
      val bigo2 = BigOr(i, A, zero, two)

      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)

      val p = solvePropositional(fseq)

      // TODO: something with these...
      solvePropositional(FSequent(Neg(And(Neg(A), Neg(B))) :: Nil, Or(A , B) :: Nil))
      solvePropositional(FSequent(Or(Or(A, B), C) :: Nil, A :: B :: C :: Nil))
      solvePropositional(FSequent(And(A , B) :: Nil, Neg(Or(Neg(A), Neg(B))) :: Nil))
      solvePropositional(FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil))
      solvePropositional(FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil))
      solvePropositional(FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil))
      
      val c2 = SchemaConst("c", Ti)
      val d2 = SchemaConst("d", Ti)
      val e2 = SchemaConst("e", Ti)
      val P = SchemaConst("P", Ti -> To)
      val Pc2 = Atom(P, c2::Nil)
      val Pd2 = Atom(P, d2::Nil)
      val Pe2 = Atom(P, e2::Nil)
      val andPc2Pd2 = And(Pc2, Pd2)
      val impPc2Pd2 = Imp(Pc2, Pd2)
      val imp_andPc2Pd2_Pe2 = Imp(andPc2Pd2, Pe2)
      val orPc2Pd2 = Or(Pc2, Pd2)
      val seq11 = FSequent(Pc2::Nil, Pc2::Nil)
      val seq12 = FSequent(andPc2Pd2::Nil, Pc2::Nil)
      val seq13 = FSequent(Pc2::Nil, orPc2Pd2::Nil)
      val seq14 = FSequent(andPc2Pd2::Nil, orPc2Pd2::Nil)
      val seq15 = FSequent(Pc2::impPc2Pd2::imp_andPc2Pd2_Pe2::Nil, Pe2::Nil)
      val seq16 = FSequent(Pc2::Nil, Pd2::Nil)

      solvePropositional(seq16) must beEqualTo (None)
    }
  }
}

