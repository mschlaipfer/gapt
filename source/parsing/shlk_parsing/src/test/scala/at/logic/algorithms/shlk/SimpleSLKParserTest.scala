/*
 * SimpleHOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.lk._
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.types.To

//import at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.language.schema._

@RunWith(classOf[JUnitRunner])
class SimpleSLKParserTest extends SpecificationWithJUnit {
  //private class MyParser extends StringReader("")
    "SimpleSLKParser" should {

      sequential
        "parse correctly a SLK-proof" in {
          val var3 = Atom(SchemaVar("x3",To), Nil)
          val var4 = Atom(SchemaVar("x4",To), Nil)
          val ax1  = Axiom(var3::Nil, var3::Nil)
          val ax2  = Axiom(var4::Nil, var4::Nil)
          val negl = NegLeftRule(ax1, var3)
          val proof  = OrLeftRule(negl, ax2, var3, var4)

//          SHLK.parseProof( "1 : ax(x3: o |- x3: o)  " +
//                            "2 : negL( 1 , x3:o)" +
//                            "3 : ax(x4: o |- x4: o)" +
//                            "4 : orL(2, 3, x3:o, x4:o)", "4").toString must beEqualTo (proof.toString)

          val A0 = IndexedPredicate("A", IntZero())
          val i = IntVar("i")
          val Ai2 = IndexedPredicate("A", Succ(Succ(i)))
          val Ai = IndexedPredicate("A", Succ(i))
          val f1 = at.logic.language.schema.And(A0, BigAnd(i,Ai,IntZero(),Succ(i)))
          val ax11 = Axiom(A0::Nil, A0::Nil)
//          println("\n\n"+ax11.root.toString)

//          SHLK.parseProof( "1 : ax(A(i+2) |- And A(0) BigAnd(i,0,s(i),A(i)))" +
//                           "2 : negR(1,A(i+2))","2").root.toString

//          SHLK.parseProof( "1 : pLink((psi,k+1) , A(0) |- A(0))","1").root.toString
//          println("\n\n")



//          val p = SHLK.parseProof(  "1 : pLink((psi,k)  A(0), BigAnd(i=0..k , (~A(i) \\/ A(i+1) ) ) |- A(k+1))" +
//                                    "2 : ax(A(k+1) |- A(k+1))" +
//                                    "3 : negL(2, A(k+1))" +
//                                    "4 : ax(A(k+2) |- A(k+2))" +
//                                    "5 : orL(3, 4, ~A(k+1), A(k+2))" +
//                                    "6 : cut(1, 5, A(k+1))" +
//                                    "root : andL(6, BigAnd(i=0..k , ( ~A(i) \\/ A(i+1) ) ), (~A(k+1) \\/ A(k+2) ) )", "root")
//          println("\n\np = "+  p.root.toString())
//          p.root.toString must beEqualTo ("(i.((¬(A(i)) ∨ A(s(i)))) ⋀ 0)(s(k)), A(0) :- A(s(s(k)))")
//          val s = Source.fromFile("/home/cvetan/gapt-trunk/source/integration_tests/simple_schema_test/src/test/resources/input1.lks").toList.foldLeft("")((ch,res) => ch + res)
//          val s = Source.fromFile("target" + separator + "test-classes" + separator + "input_multi_indxs.lks").toList.foldLeft("")((ch,res) => ch + res)
          val s = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "adder.lks"))

          val map = SHLK.parseProof(s)
//          println("\n\np = "+  map.get("chi").get._1.get("root").get.root.toString()  )
//                       val p = map.get("chi").get._2.get("root").get
//          println("\n\npsi_b = "+  map.get("psi").get._1.get("root").get.root.toString()  )
//          println("\n\npsi_s = "+  map.get("psi").get._2.get("root").get.root.toString()  )
//          println("\n\nchi_b = "+  map.get("chi").get._1.get("root").get.root.toString()  )
//          println("\n\nchi_s = "+  map.get("chi").get._2.get("root").get.root.toString()  )
//          println("\n\nphi_b = "+  map.get("phi").get._1.get("root").get.root.toString()  )
//          println("\n\nphi_s = "+  map.get("phi").get._2.get("root").get.root.toString()  )
//          Main.display("Proof", map.head._2._1) ; while(true){}

//          Main.display("phi", map.get("phi").get._2.get("root").get) ;


//          val seq = SHLK.parseSequent("P(n,f(0,x)) |- ")
//          val seq = SHLK.parseSequent("Forall x P(f(k,x)), P(x(k)) |- ")
//          println(seq)


          	// specs2 require a least one Result, see org.specs2.specification.Example 
          	Success()

        }
    }
}
