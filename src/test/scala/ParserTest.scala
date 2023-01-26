import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {

  private inline def roundtrip[T](parseable: Parseable[T], string: String): Unit = {
    s"${parseable.getClass.getName.replace("$", "")} should roundtrip '$string'" in {
      val pc = StringParseContext(string)
      val v = parseable.parse(pc)
      assert(v.toString == string)
    }
  }

  private inline def raise[T](parseable: Parseable[T], string: String, err: String): Unit = {
    s"${parseable.getClass.getName.replace("$", "")} should raise '$err' when parsing '$string'" in {
      val pc = StringParseContext(string)
      val ex = intercept[ParseException]{ parseable.parse(pc) }
      assert(ex.msg == err)
    }
  }

  roundtrip(Value, "foo")
  roundtrip(Value, "<>")
  roundtrip(Value, "<foo, bar>")
  roundtrip(Value, "inl foo")
  roundtrip(Value, "inr bar")
  roundtrip(Value, "into(baz)")
  roundtrip(Value, "{return hello}")
  raise(Value, "<", "unexpected EOF")
  raise(Value, "return <>", "unexpected 'return' (expecting a value)")

  roundtrip(Head, "foo")
  roundtrip(Head, "[<> : 1]")
  raise(Head, "(return <> : ↑1)", "unexpected '(' (expecting a head)")

  roundtrip(BoundExpression, "foo()")
  roundtrip(BoundExpression, "foo(bar)")
  roundtrip(BoundExpression, "foo(bar,baz)")
  roundtrip(BoundExpression, "[{λx . return x} : ↓(1 → ↑1)](<>)")
  roundtrip(BoundExpression, "(return <> : ↑1)")
  raise(BoundExpression, "<>", "unexpected '<' (expecting a head)")
  raise(BoundExpression, "[<> : 1]", "unexpected EOF")

  roundtrip(Expression, "return <>")
  roundtrip(Expression, "let x = (return <> : ↑1); return x")
  roundtrip(Expression, "match x {}")
  roundtrip(Expression, "match x {<> ⇒ return y}")
  roundtrip(Expression, "match x {<l, r> ⇒ return <r, l>}")
  roundtrip(Expression, "match x {inl l ⇒ return l | inr r ⇒ return r}")
  roundtrip(Expression, "match x {into(y) ⇒ return y}")
  roundtrip(Expression, "λx . return <x, x>")
  roundtrip(Expression, "rec x : (1 → ↑1) . λy . let z = x(y); return z")
  raise(Expression, "{return <>}", "unexpected '{' (expecting an expression)")

  roundtrip(PType, "0")
  roundtrip(PType, "1")
  roundtrip(PType, "(1 × 0)")
  roundtrip(PType, "(0 + 1)")
  roundtrip(PType, "↓↑1")
  // TODO roundtrip(PType, "{???}")
  // TODO roundtrip(PType, "∃a : τ . 1")
  // TODO roundtrip(PType, "(1 ∧ ψ)")

  roundtrip(NType, "↑1")
  roundtrip(NType, "(1 → ↑1)")
  roundtrip(NType, "(1 → (1 → ↑1))")
  // TODO roundtrip(PType, "∀a : τ . 1")
  // TODO roundtrip(PType, "(ψ ⊃ ↑1)")

}
