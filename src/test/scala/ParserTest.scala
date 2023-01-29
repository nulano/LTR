import scala.reflect.ClassTag

import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {

  private inline def roundtrip[T](parseable: Parseable[? >: T], string: String)(implicit tp: ClassTag[T]): Unit = {
    s"${parseable.getClass.getName.replace("$", "")} should roundtrip '$string' as $tp" in {
      val pc = StringParseContext(string)
      val v = parseable.parse(pc)
      assert(v.toString == string)
      assert(tp.runtimeClass.isAssignableFrom(v.getClass), s"wrong result type: expected $tp, got ${v.getClass.getName}")
    }
  }

  private inline def roundtripMatch[T <: MatchPattern](string: String)(implicit tp: ClassTag[T]): Unit = {
    s"Expression should roundtrip '$string' as ExpMatch with $tp" in {
      val pc = StringParseContext(string)
      val v = Expression.parse(pc)
      assert(v.toString == string)
      v match {
        case ExpMatch(_, clauses) => assert(tp.runtimeClass.isAssignableFrom(clauses.getClass), s"wrong clauses type: expected $tp, got ${v.getClass.getName}")
        case _ => fail(s"wrong result type: expected ExpMatch, got ${v.getClass.getName}")
      }
    }
  }

  private inline def raise[T](parseable: Parseable[T], string: String, err: String): Unit = {
    s"${parseable.getClass.getName.replace("$", "")} should raise '$err' when parsing '$string'" in {
      val pc = StringParseContext(string)
      val ex = intercept[ParseException]{ parseable.parse(pc) }
      assert(ex.msg == err)
    }
  }

  roundtrip[ValVariable](Value, "foo")
  roundtrip[ValUnit](Value, "<>")
  roundtrip[ValPair](Value, "<foo, bar>")
  roundtrip[ValLeft](Value, "inl foo")
  roundtrip[ValRight](Value, "inr bar")
  roundtrip[ValInto](Value, "into(baz)")
  roundtrip[ValExpression](Value, "{return hello}")
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

  roundtrip[ExpReturn](Expression, "return <>")
  roundtrip[ExpLet](Expression, "let x = (return <> : ↑1); return x")
  roundtripMatch[MPVoid]("match x {}")
  roundtripMatch[MPUnit]("match x {<> ⇒ return y}")
  roundtripMatch[MPProd]("match x {<l, r> ⇒ return <r, l>}")
  roundtripMatch[MPSum]("match x {inl l ⇒ return l | inr r ⇒ return r}")
  roundtripMatch[MPInto]("match x {into(y) ⇒ return y}")
  roundtrip[ExpFunction](Expression, "λx . return <x, x>")
  roundtrip[ExpRecursive](Expression, "rec x : (1 → ↑1) . λy . let z = x(y); return z")
  raise(Expression, "{return <>}", "unexpected '{' (expecting an expression)")

  roundtrip[PVoid](PType, "0")
  roundtrip[PUnit](PType, "1")
  roundtrip[PProd](PType, "(1 × 0)")
  roundtrip[PSum](PType, "(0 + 1)")
  roundtrip[PSuspended](PType, "↓↑1")
  // TODO roundtrip(PType, "{???}")
  // TODO roundtrip(PType, "∃a : τ . 1")
  // TODO roundtrip(PType, "(1 ∧ ψ)")

  roundtrip[NComputation](NType, "↑1")
  roundtrip[NFunction](NType, "(1 → ↑1)")
  roundtrip[NFunction](NType, "(1 → (1 → ↑1))")
  // TODO roundtrip(PType, "∀a : τ . 1")
  // TODO roundtrip(PType, "(ψ ⊃ ↑1)")

}
