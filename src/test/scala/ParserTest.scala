import scala.reflect.ClassTag

import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {

  private def parseableName[T](parseable: Parseable[T]): String = {
    parseable.getClass.getName.replace("$", "")
  }

  private inline def parseTo[T](parseable: Parseable[? >: T], string: String, norm: String)(implicit tp: ClassTag[T]): Unit = {
    s"${parseableName(parseable)}.parse('$string') should return $tp '$norm' which roundtrips" in {
      val v = parseable.parse(StringParseContext(string))
      assert(v.toString == norm)
      assert(tp.runtimeClass.isAssignableFrom(v.getClass), s"wrong result type: expected $tp, got ${v.getClass.getName}")
      val w = parseable.parse(StringParseContext(norm))
      assert(w == v)
    }
  }

  private inline def roundtrip[T](parseable: Parseable[? >: T], string: String)(implicit tp: ClassTag[T]): Unit = {
    s"${parseableName(parseable)}.parse('$string') should return $tp and roundtrip" in {
      val v = parseable.parse(StringParseContext(string))
      assert(v.toString == string)
      assert(tp.runtimeClass.isAssignableFrom(v.getClass), s"wrong result type: expected $tp, got ${v.getClass.getName}")
    }
  }

  private inline def parseMatch[T <: MatchPattern](string: String, norm: String)(implicit tp: ClassTag[T]): Unit = {
    s"Expression.parse('$string') should return ExpMatch '$norm' with $tp which roundtrip" in {
      val v = Expression.parse(StringParseContext(string))
      assert(v.toString == norm)
      v match {
        case ExpMatch(_, clauses) => assert(tp.runtimeClass.isAssignableFrom(clauses.getClass), s"wrong clauses type: expected $tp, got ${v.getClass.getName}")
        case _ => fail(s"wrong result type: expected ExpMatch, got ${v.getClass.getName}")
      }
      val w = Expression.parse(StringParseContext(norm))
      assert(w == v)
    }
  }

  private inline def raise[T](parseable: Parseable[T], string: String, err: String): Unit = {
    s"${parseableName(parseable)} should raise '$err' when parsing '$string'" in {
      val pc = StringParseContext(string)
      val ex = intercept[ParseException]{ parseable.parse(pc) }
      assert(ex.msg == err)
    }
  }

  roundtrip[ValVariable](Value, "foo")
  parseTo[ValUnit](Value, " < \t\r\n   > ", "<>")
  parseTo[ValPair](Value, "  < foo  ,bar\t>", "<foo, bar>")
  parseTo[ValLeft](Value, "inj1\nfoo", "inl foo")
  parseTo[ValRight](Value, "inj₂  bar", "inr bar")
  parseTo[ValInto](Value, "into ( baz )", "into(baz)")
  parseTo[ValExpression](Value, "{  return hello  }", "{return hello}")
  raise(Value, "<", "unexpected EOF")
  raise(Value, "return <>", "unexpected 'return' (expecting a value)")

  roundtrip[HeadVariable](Head, "foo")
  roundtrip[HeadValue](Head, "[<> : 1]")
  raise(Head, "(return <> : ↑1)", "unexpected '(' (expecting a head)")

  roundtrip[BEApplication](BoundExpression, "foo()")
  roundtrip[BEApplication](BoundExpression, "foo(bar)")
  roundtrip[BEApplication](BoundExpression, "foo(bar,baz)")
  roundtrip[BEApplication](BoundExpression, "[{λx . return x} : ↓(1 → ↑1)](<>)")
  roundtrip[BEExpression](BoundExpression, "(return <> : ↑1)")
  raise(BoundExpression, "<>", "unexpected '<' (expecting a head)")
  raise(BoundExpression, "[<> : 1]", "unexpected EOF")
  raise(BoundExpression, "foo(,)", "unexpected ',' (expecting a value)")
  raise(BoundExpression, "foo(bar,)", "unexpected ')' (expecting a value)")
  raise(BoundExpression, "foo(bar,baz,)", "unexpected ')' (expecting a value)")
  raise(BoundExpression, "foo(bar,,baz)", "unexpected ',' (expecting a value)")
  raise(BoundExpression, "foo(bar baz)", "unexpected 'baz' (expecting ',' or ')')")

  parseTo[ExpReturn](Expression, "return<>", "return <>")
  parseTo[ExpLet](Expression, "let x=(  return <> : ↑1  )  ;return x", "let x = (return <> : ↑1); return x")
  parseMatch[MPVoid]("match x{   }", "match x {}")
  parseMatch[MPUnit]("match x{  <  >=>return y\t}", "match x {<> ⇒ return y}")
  parseMatch[MPProd]("match x\n{<  l ,r > =>\nreturn <r, l>}", "match x {<l, r> ⇒ return <r, l>}")
  parseMatch[MPSum]("match x{inj1l=>return l || inj₂r ⇒ return r}", "match x {inl l ⇒ return l ‖ inr r ⇒ return r}")
  parseMatch[MPInto]("match x    { into  (  y  )=> return y}", "match x {into(y) ⇒ return y}")
  parseTo[ExpFunction](Expression, "fun  x.return <x,x>", "λx . return <x, x>")
  roundtrip[ExpRecursive](Expression, "rec x : (1 → ↑1) . λy . let z = x(y); return z")
  raise(Expression, "{return <>}", "unexpected '{' (expecting an expression)")

  parseTo[FIdentity](FunctorBase, "id", "Id")
  parseTo[FConstant](FunctorBase, "[ 1 ]", "[1]")
  parseTo[FUnit](FunctorProduct, " I ", "I")
  parseTo[FProduct](FunctorProduct, "( [ 1 ] (X)(Id(X)I))", "([1] ⊗ (Id ⊗ I))")
  parseTo[FSum](FunctorSum, "( ( I (+) (Id⊗I) )(+)(I(+)I) )", "((I ⊕ (Id ⊗ I)) ⊕ (I ⊕ I))")

  parseTo[SBool](Sort, "B", "𝔹")
  parseTo[SNat](Sort, "N", "ℕ")
  parseTo[SInt](Sort, "Z", "ℤ")
  parseTo[SProd](Sort, "(ZXB)", "(ℤ × 𝔹)")
  parseTo[SProd](Sort, "(ZX(BXN))", "(ℤ × (𝔹 × ℕ))")
  raise(Sort, "<>", "unexpected '<' (expecting a sort)")

  roundtrip[PVoid](PType, "0")
  roundtrip[PUnit](PType, "1")
  parseTo[PProd](PType, "( 1X0 )", "(1 × 0)")
  parseTo[PSum](PType, "(0+1)", "(0 + 1)")
  parseTo[PSuspended](PType, "V^1", "↓↑1")
  // TODO roundtrip(PType, "{???}")
  parseTo[PInductive](PType, "fix I S alg => idx", "μI ⊃ alg ⇒ idx")
  parseTo[PExists](PType, "Ea:B.1", "∃a : 𝔹 . 1")
  // TODO roundtrip(PType, "(1 ∧ ψ)")
  raise(PType, "μ[1] ⊃ alg ⇒ idx", "not a sum functor")

  parseTo[NComputation](NType, "^ 1", "↑1")
  parseTo[NFunction](NType, "( 1->^1 )", "(1 → ↑1)")
  parseTo[NFunction](NType, "(1->(1->^1))", "(1 → (1 → ↑1))")
  parseTo[NForAll](NType, "Aa:N.^1", "∀a : ℕ . ↑1")
  // TODO roundtrip(NType, "(ψ ⊃ ↑1)")

}
