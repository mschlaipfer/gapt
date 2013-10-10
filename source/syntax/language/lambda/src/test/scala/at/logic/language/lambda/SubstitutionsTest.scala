/*
 * SubstitutionsTest.scala
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import types._
import symbols._
import types.Definitions._
import BetaReduction._
import ImplicitStandardStrategy._
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class SubstitutionsTest extends SpecificationWithJUnit {

  "Substitutions" should {
    "NOT compose the substitution {f(y)/x} and {g(y)/x}" in {
      val x = Var("x", i);
      val y = Var("y", i);
      val f = Var("f", i -> i)
      val g = Var("g", i -> i)
      val e1 = App(f, y)
      val e2 = App(g, y)
      val sub1 = Substitution(x,e1)
      val sub2 = Substitution(x,e2)
      val sub = sub1 compose sub2
      sub must beEqualTo (sub2)
    }
    "substitute correctly when Substitution is applied (1)" in {
      val v = Var("v", i); 
      val x = Var("x", i); 
      val f = Var("f", i -> i)
      val e = App(f, x)
      val sigma = Substitution(v, e)
      ( e ) must beEqualTo ( sigma( v.asInstanceOf[LambdaExpression] ) )
    }
    "substitute correctly when Substitution is applied (2)" in {
      val v = Var("v", i); val x = Var("x", i); val f = Var("f", i -> i)
      val e = App(f, x)
      val sigma = Substitution(v, e)
      val expression = App(f, v)
      ( App(f, App(f, x)) ) must beEqualTo ( sigma(expression) )
    }
    "substitute correctly when Substitution is applied (3)" in {
      val v = Var("v", i); val x = Var("x", i); val f = Var("f", i -> i)
      val y = Var("y", i)
      val e = App(f, x)
      val sigma = Substitution(v,e)
      val expression = Abs(y, App(f, v))
      ( Abs(y,App(f, App(f, x))) ) must beEqualTo ( sigma(expression) )
    }
    "substitute correctly when SingleSubstitution is applied, renaming bound variables (1)" in {
        val v = Var("v", i); 
        val x = Var("x", i); 
        val f = Var("f", i -> i)
        val e = App(f, x)
        val sigma = Substitution(v,e)
        val exp1 = Abs(x, App(f, v))
        val exp2 = sigma(exp1)
        val exp3 = Abs(x,App(f, App(f, x)))
        ( exp2 ) must be_!= ( exp3 )
    }
    "substitute correctly when SingleSubstitution is applied, renaming bound variables (2)" in {
        val v = Var("v", i); val x = Var("x", i); val f = Var("f", i -> i)
        val e = App(f, x)
        val sigma = Substitution(v,e)
        val exp1 = Abs(f, App(f, v))
        val exp2 = sigma(exp1)
        val exp3 = Abs(f,App(f, App(f, x)))
        ( exp2) must be_!= ( exp3 )
    }
    "substitute and normalize correctly when Substitution is applied" in {
      val x = Var("X", i -> o )
      val f = Var("f", (i -> o) -> i )
      val xfx = App(x, App( f, x ) )

      val z = Var("z", i)
      val p = Var("P", i -> o)
      val Pz = App( p, z )
      val t = Abs( z, Pz )

      val sigma = Substitution( x, t )

      betaNormalize( sigma.apply( xfx ) ) must beEqualTo( App( p, App( f, t ) ) )
    }
    "concatenate/compose 2 Substitutions correctly" in {
      val v = Var("v", i); val x = Var("x", i); val f = Var("f", i -> i)
      val e = App(f, x)
      val sigma = Substitution(v,e)
      val sigma1 = sigma::(Substitution())
      val sigma2 = sigma::sigma::(Substitution())
      val sigma3 = sigma1::sigma1
      ( sigma2 ) must beEqualTo ( sigma3 )
    }
    "substitute correctly when Substitution is applied" in {
      val v = Var("v", i)
      val x = Var("x", i)
      val f = Var("f", i -> i)
      val e = App(f, v)
      val sigma1 = Substitution(v,x)
      ( sigma1(e) ) must beEqualTo ( App(f,x) )
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> gy}" in {
      val term1 = App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("x",i))
      val sub = Substitution(Var("x",i), App(Var("g",i->i),Var("y",i)))
      val term2 = App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),App(Var("g",i->i),Var("y",i)))
      (sub(term1)) must beEqualTo (term2)
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> (\\x.fx)c}" in {
      "- 1" in {
        val term1 = App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("x",i))
        val sub = Substitution(Var("x",i), App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("c",i)))
        val term2 = App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("c",i)))
        (sub(term1)) must beEqualTo (term2)
      }
      "- 2" in {
        val term1 = App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("x",i))
        val sub = Substitution(Var("x",i), App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("c",i)))
        val term2 = App(Abs(Var("z",i), App(Var("f",i->i),Var("z",i))),App(Abs(Var("w",i), App(Var("f",i->i),Var("w",i))),Var("c",i)))
        (sub(term1)) must beEqualTo (term2)
      }
    }
    "substitute correctly when substituting a term with bound variables into the scope of other bound variables" in {
      val term1 = Abs(Var("x",i), App(Var("F",i->i),Var("x",i)))
      val sub = Substitution(Var("F",i->i), Abs(Var("x",i), App(Var("f",i->i),Var("x",i))))
      val term2 = Abs(Var("x",i), App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("x",i)))
      (sub(term1)) must beEqualTo (term2)
    }
    "work correctly on subterms of abs (i.e. the variables which were bound there are no longer bound)" in {
      val term1 = Abs(Var("F",i->i),Abs(Var("x",i), App(Var("F",i->i),Var("x",i))))
      val sub = Substitution(term1.variable, Abs(Var("x",i), App(Var("f",i->i),Var("x",i))))
      val term2 = Abs(Var("x",i), App(Abs(Var("x",i), App(Var("f",i->i),Var("x",i))),Var("x",i)))
      (sub(term1.term)) must beEqualTo (term2)
    }
    "not substitute terms with different types" in {
      val x = Var("x", i)
      val f = Var("f", i -> i)
      val e = App(f, x)
      val g = Var("g", i)
      val result = try { Substitution(f, g); false } catch {
        case ex: IllegalArgumentException => true
        case _ => false
      }

      result must beTrue
    }
    "not substitute variables with different types" in {
      val x = Var("x", i -> i)
      val c = Var("c", i)
      val result = try { Substitution(x, c); false } catch {
        case ex: IllegalArgumentException => true
        case _ => false
      }

      result must beTrue
    }
  }
}
