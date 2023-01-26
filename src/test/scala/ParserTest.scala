import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {

  private inline def roundtrip[T](parseable: Parseable[T], string: String): Unit = {
    s"${parseable.getClass.getName.replace("$", "")} should roundtrip '$string'" in {
      val pc = StringParseContext(string)
      val v = parseable.parse(pc)
      assert(v.toString == string)
    }
  }

  roundtrip(Value, "foo")
  roundtrip(Value, "<>")
  roundtrip(Value, "<foo, bar>")
  roundtrip(Value, "inl foo")
  roundtrip(Value, "inr bar")
  roundtrip(Value, "into(baz)")
  roundtrip(Value, "{return hello}")

  roundtrip(Head, "foo")
  roundtrip(Head, "[<> : 1]")

  roundtrip(BoundExpression, "foo()")
  roundtrip(BoundExpression, "foo(bar)")
  roundtrip(BoundExpression, "foo(bar,baz)")
  roundtrip(BoundExpression, "[{λx . return x} : ↓(1 → ↑1)](<>)")
  roundtrip(BoundExpression, "(return <> : ↑1)")

  roundtrip(Expression, "return <>")
  roundtrip(Expression, "let x = (return <> : ↑1); return x")
  roundtrip(Expression, "match x {}")
  roundtrip(Expression, "match x {<> ⇒ return y}")
  roundtrip(Expression, "match x {<l, r> ⇒ return <r, l>}")
  roundtrip(Expression, "match x {inl l ⇒ return l | inr r ⇒ return r}")
  roundtrip(Expression, "match x {into(y) ⇒ return y}")
  roundtrip(Expression, "λx . return <x, x>")
  roundtrip(Expression, "rec x : (1 → ↑1) . λy . let z = x(y); return z")

}
