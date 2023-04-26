import scala.reflect.ClassTag

import org.scalatest.freespec.AnyFreeSpec

class ParserTest extends AnyFreeSpec {

  private def parseableName[T](parseable: Parseable[T]): String = {
    parseable.getClass.getName.replace("$", "")
  }

  private def removeVarSuffixes(s: String): String = s.filter(c => c < '₀' | c > '₉')

  private inline def parseTo[T](parseable: Parseable[? >: T], string: String, norm: String, indexVars: List[IndexVariable] = List.empty)(implicit tp: ClassTag[T]): Unit = {
    s"${parseableName(parseable)}.parse('$string') should return $tp '$norm' which roundtrips" in {
      val pc = ParseContext(Parser.forString("test", string), indexVars = indexVars.map{case i => (i.name, i)}.toMap)
      val v = parseable.parse(pc)
      assert(pc.pop(Tk.EOF).tk == Tk.EOF)
      assert(removeVarSuffixes(v.toString) == norm)
      assert(tp.runtimeClass.isAssignableFrom(v.getClass), s"wrong result type: expected $tp, got ${v.getClass.getName}")
      val w = parseable.parse(ParseContext(Parser.forString("test", norm), indexVars = indexVars.map{case i => (i.name, i)}.toMap))
      assert(w == v)
    }
  }

  private inline def roundtrip[T](parseable: Parseable[? >: T], string: String, indexVars: List[IndexVariable] = List.empty)(implicit tp: ClassTag[T]): Unit = {
    s"${parseableName(parseable)}.parse('$string') should return $tp and roundtrip" in {
      val pc = ParseContext(Parser.forString("test", string), indexVars = indexVars.map{case i => (i.name, i)}.toMap)
      val v = parseable.parse(pc)
      assert(pc.pop(Tk.EOF).tk == Tk.EOF)
      assert(removeVarSuffixes(v.toString) == string)
      assert(tp.runtimeClass.isAssignableFrom(v.getClass), s"wrong result type: expected $tp, got ${v.getClass.getName}")
    }
  }

  private inline def parseMatch[T <: MatchPattern](string: String, norm: String)(implicit tp: ClassTag[T]): Unit = {
    s"Expression.parse('$string') should return ExpMatch '$norm' with $tp which roundtrip" in {
      val pc = ParseContext(Parser.forString("test", string))
      val v = Expression.parse(pc)
      assert(pc.pop(Tk.EOF).tk == Tk.EOF)
      assert(removeVarSuffixes(v.toString) == norm)
      v match {
        case ExpMatch(_, clauses) => assert(tp.runtimeClass.isAssignableFrom(clauses.getClass), s"wrong clauses type: expected $tp, got ${v.getClass.getName}")
        case _ => fail(s"wrong result type: expected ExpMatch, got ${v.getClass.getName}")
      }
      val w = Expression.parse(ParseContext(Parser.forString("test", norm)))
      assert(w == v)
    }
  }

  private inline def raise[T](parseable: Parseable[T], string: String, err: String, indexVars: List[IndexVariable] = List.empty): Unit = {
    s"${parseableName(parseable)} should raise '$err' when parsing '$string'" in {
      val pc = ParseContext(Parser.forString("test", string), indexVars = indexVars.map{case i => (i.name, i)}.toMap)
      val ex = intercept[ParseException]{ parseable.parse(pc) }
      assert(ex.msg == err)
    }
  }

  roundtrip[ValVariable](Value, "foo")
  roundtrip[ValVariable](Value, "fooBar")
  roundtrip[ValVariable](Value, "foo_Bar42_X")
  parseTo[ValUnit](Value, " < \t\r\n   > ", "<>")
  parseTo[ValPair](Value, "  < foo  ,bar\t>", "<foo, bar>")
  parseTo[ValLeft](Value, "inj1\nfoo", "inl foo")
  parseTo[ValRight](Value, "inj₂  bar", "inr bar")
  parseTo[ValInto](Value, "into ( baz )", "into(baz)")
  parseTo[ValExpression](Value, "{  return hello  }", "{return hello}")
  raise(Value, "HI", "unexpected 'H' (expecting a value)")
  raise(Value, "<", "unexpected '<end-of-file>' (expecting a value)")
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
  raise(BoundExpression, "[<> : 1]", "unexpected '<end-of-file>' (expecting '(')")
  raise(BoundExpression, "foo(,)", "unexpected ',' (expecting a value)")
  raise(BoundExpression, "foo(bar,)", "unexpected ')' (expecting a value)")
  raise(BoundExpression, "foo(bar,baz,)", "unexpected ')' (expecting a value)")
  raise(BoundExpression, "foo(bar,,baz)", "unexpected ',' (expecting a value)")
  raise(BoundExpression, "foo(bar baz)", "unexpected 'baz' (expecting ',' or ')')")

  parseTo[ExpReturn](Expression, "return<>", "return <>")
  parseTo[ExpLet](Expression, "let x=(  return <> : ↑1  )  ;return x", "let x = (return <> : ↑1); return x")
  parseMatch[MPVoid]("match x{   }", "match x {}")
  parseMatch[MPUnit]("match x{  <  > =>return y\t}", "match x {<> ⇒ return y}")
  parseMatch[MPProd]("match x\n{<  l ,r > =>\nreturn <r, l>}", "match x {<l, r> ⇒ return <r, l>}")
  parseMatch[MPSum]("match x{inj1l=>return l || inj₂r ⇒ return r}", "match x {inl l ⇒ return l ‖ inr r ⇒ return r}")
  parseMatch[MPSum]("match x{inr r=>return r || inj₁l ⇒ return l}", "match x {inl l ⇒ return l ‖ inr r ⇒ return r}")
  parseMatch[MPInto]("match x    { into  (  y  )=> return y}", "match x {into(y) ⇒ return y}")
  parseTo[ExpFunction](Expression, "fun  x.return <x,x>", "λx . return <x, x>")
  roundtrip[ExpRecursive](Expression, "rec x : (1 → ↑1) . λy . let z = x(y); return z")
  raise(Expression, "{return <>}", "unexpected '{' (expecting an expression)")

  parseTo[FIdentity.type](FunctorBase, "id", "Id")
  parseTo[FConstant](FunctorBase, "[ 1 ]", "[1]")
  parseTo[FUnit.type](FunctorProduct, " I ", "I")
  parseTo[FProduct](FunctorProduct, "( [ 1 ] (X)(id(X)I))", "([1] ⊗ (Id ⊗ I))")
  parseTo[FSum](FunctorSum, "( ( I (+) (Id⊗I) )(+)(I(+)I) )", "((I ⊕ (Id ⊗ I)) ⊕ (I ⊕ I))")
  raise(Functor, "<>", "unexpected '<' (expecting a functor)")
  raise(FunctorSum, "Id", "not a sum functor")
  raise(FunctorProduct, "(I ⊕ I)", "not a product functor")
  raise(FunctorBase, "(I ⊕ I)", "not a base functor")

  roundtrip[APConstant.type](AlgebraBasePattern, "_")
  roundtrip[APIdentity](AlgebraBasePattern, "foo")
  roundtrip[APPack](AlgebraBasePattern, "pack(foo, _)")
  roundtrip[APPack](AlgebraBasePattern, "pack(foo, bar)")
  roundtrip[APPack](AlgebraBasePattern, "pack(foo, pack(bar, _))")
  roundtrip[APPack](AlgebraBasePattern, "pack(foo, pack(bar, baz))")
  raise(AlgebraBasePattern, "()", "unexpected '(' (expecting a base algebra pattern)")

  roundtrip[APUnit.type](AlgebraProductPattern, "()")
  roundtrip[APProduct](AlgebraProductPattern, "(pack(foo, bar), ())")
  roundtrip[APProduct](AlgebraProductPattern, "(pack(foo, bar), (baz, ()))")
  raise(AlgebraProductPattern, "inl ()", "unexpected 'inl' (expecting a product algebra pattern)")
  raise(AlgebraProductPattern, "(inl (), ())", "unexpected 'inl' (expecting a base algebra pattern)")
  raise(AlgebraProductPattern, "(_, inl ())", "unexpected 'inl' (expecting a product algebra pattern)")

  parseTo[APLeft](AlgebraSumPattern, "inj₁()", "inl ()")
  parseTo[APRight](AlgebraSumPattern, "inj2(_ ,(   ))", "inr (_, ())")
  raise(AlgebraSumPattern, "_", "unexpected '_' (expecting a sum algebra pattern)")

  parseTo[AlgebraProd](Algebra, "(()=>42)", "(() ⇒ 42)")
  parseTo[AlgebraProd](Algebra, "((_,())=>42)", "((_, ()) ⇒ 42)")
  parseTo[AlgebraSum](Algebra, "(inj₂()=>(T∨F)||inj1(_,())=>42)", "(inl (_, ()) ⇒ 42 ‖ inr () ⇒ (T ∨ F))")
  parseTo[AlgebraSum](Algebra,
    "(inr inr (rr, ()) ⇒ 3 ‖ inl inr (lr, ()) ⇒ 1 ‖ inl inl (ll, ()) ⇒ 0 ‖ inr inl (rl, ()) ⇒ 2)",
    "(inl inl (ll, ()) ⇒ 0 ‖ inl inr (lr, ()) ⇒ 1 ‖ inr inl (rl, ()) ⇒ 2 ‖ inr inr (rr, ()) ⇒ 3)")
  raise(Algebra, "()", "unexpected ')' (expecting a sum algebra pattern)")
  raise(Algebra, "( ‖ () ⇒ 1)", "unexpected '‖' (expecting a sum algebra pattern)")
  raise(Algebra, "(inl () ⇒ 1 ‖ inr () ⇒ 2 ‖ )", "unexpected ')' (expecting a sum algebra pattern)")
  raise(Algebra, "(inl () ⇒ 1 ‖ ‖ inr () ⇒ 2)", "unexpected '‖' (expecting a sum algebra pattern)")
  raise(Algebra, "(() ⇒ a)", "index variable is not bound", List(new IVBound("a", SNat)))

  parseTo[SBool.type](Sort, "B", "𝔹")
  parseTo[SNat.type](Sort, "N", "ℕ")
  parseTo[SInt.type](Sort, "Z", "ℤ")
  parseTo[SProd](Sort, "(ZXB)", "(ℤ × 𝔹)")
  parseTo[SProd](Sort, "(ZX(BXN))", "(ℤ × (𝔹 × ℕ))")
  raise(Sort, "<>", "unexpected '<' (expecting a sort)")

  roundtrip[IVariable](Index, "foo", indexVars = List(new IVBound("foo", SNat)))
  roundtrip[INatConstant](Index, "42")
  roundtrip[IIntConstant](Index, "+42")
  roundtrip[IIntConstant](Index, "-42")
  roundtrip[ISum](Index, "(foo + bar)", indexVars = List(new IVBound("foo", SNat), new IVBound("bar", SNat)))
  parseTo[IDifference](Index, "(a-1)", "(a - 1)", indexVars = List(new IVBound("a", SInt)))
  parseTo[IPair](Index, "( 1,2 )", "(1, 2)")
  parseTo[ILeft](Index, "π₁ foo", "L foo", indexVars = List(new IVBound("foo", SProd(SNat, SInt))))
  parseTo[IRight](Index, "π2foo", "R foo", indexVars = List(new IVBound("foo", SProd(SNat, SInt))))
  parseTo[IPEqual](Proposition, "( foo=bar )", "(foo = bar)", indexVars = List(new IVBound("foo", SNat), new IVBound("bar", SNat)))
  parseTo[IPNotEqual](Proposition, "( 1!=2 )", "(1 ≠ 2)")
  parseTo[IPLess](Proposition, "( 1<2 )", "(1 < 2)")
  parseTo[IPLessEqual](Proposition, "( 1<=2 )", "(1 ≤ 2)")
  parseTo[IPGreater](Proposition, "( 1>2 )", "(1 > 2)")
  parseTo[IPGreaterEqual](Proposition, "( 1>=2 )", "(1 ≥ 2)")
  parseTo[IPAnd](Proposition, "( T&F )", "(T ∧ F)")
  parseTo[IPOr](Proposition, "( (1=a)|(a<=2) )", "((1 = a) ∨ (a ≤ 2))", indexVars = List(new IVBound("a", SInt)))
  roundtrip[IPNot](Proposition, "¬F")
  parseTo[IPTrue.type](Proposition, "⊤", "T") // TODO reverse this
  parseTo[IPFalse.type](Proposition, "⊥", "F") // TODO reverse this
  raise(Index, "<>", "unexpected '<' (expecting an index term)")
  raise(Proposition, "foo", "not a proposition", indexVars = List(new IVBound("foo", SNat)))
  raise(Index, "(5∧F)", "not a proposition")
  raise(Index, "(T∨bar)", "not a proposition", indexVars = List(new IVBound("bar", SNat)))
  raise(Index, "¬42", "not a proposition")
  raise(Index, "foo", "index variable is not bound")

  roundtrip[PVoid.type](PType, "0")
  roundtrip[PUnit.type](PType, "1")
  parseTo[PProd](PType, "( 1X0 )", "(1 × 0)")
  parseTo[PSum](PType, "(0+1)", "(0 + 1)")
  parseTo[PSuspended](PType, "V^1", "↓↑1")
  // TODO roundtrip(PType, "{v : μF | (fold_F alg) v =_τ idx}")
  // TODO algebra does not see outer vars
  parseTo[PInductive](PType, "fix I S (()=>(7-1)) => (1+a)", "μI ⊃ (() ⇒ (7 - 1)) ⇒ (1 + a)", indexVars = List(new IVBound("a", SInt)))
  parseTo[PExists](PType, "Ea:B.1", "∃a : 𝔹 . 1")
  roundtrip[PExists](PType, "∃b : ℕ . μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a)) ⇒ b") // ∃b : ℕ . Nat(b)
  parseTo[PProperty](PType, "(1&[ F ])", "(1 ∧ [F])")
  parseTo[PExists](PType, "Ea:N.(1&[(a=5)])", "∃a : ℕ . (1 ∧ [(a = 5)])")
  raise(PType, "μ[1] ⊃ (()=>1) ⇒ idx", "not a sum functor")
  raise(PType, "↑1", "unexpected '↑' (expecting a positive type)")

  parseTo[NComputation](NType, "^ 1", "↑1")
  parseTo[NFunction](NType, "( 1->^1 )", "(1 → ↑1)")
  parseTo[NFunction](NType, "(1->(1->^1))", "(1 → (1 → ↑1))")
  parseTo[NForAll](NType, "Aa:N.^1", "∀a : ℕ . ↑1")
  parseTo[NPrecondition](NType, "[ T ]S^0", "[T] ⊃ ↑0")
  parseTo[NForAll](NType, "Aa : N . [(T | F)] S ^1", "∀a : ℕ . [(T ∨ F)] ⊃ ↑1")
  raise(NType, "(1 × 1)", "unexpected '×' (expecting '→')")
  raise(NType, "↓↑1", "unexpected '↓' (expecting a negative type)")

  roundtrip[REPLLet](REPLCommand, "let x = (return <> : ↑1)")
  roundtrip[REPLDef](REPLCommand, "def x : ↑1 = return <>")
  roundtrip[REPLRec](REPLCommand, "rec x : ∀a : ℕ . ↑1 = return <>")
  roundtrip[REPLAlgebra](REPLCommand, "alg ixnat = (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a))")
  roundtrip[REPLType](REPLCommand, "type unit = 1")
  roundtrip[REPLTypeInductive](REPLCommand, "type nat(n : ℕ) = μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a)) ⇒ n")
  raise(REPLCommand, "return <>", "unexpected 'return' (expecting a REPL statement)")
  raise(REPLCommand, "type nat(n:N) = 1", "expected an inductive type")

  // TODO separate test file?
  "PType.parse('foo') should return PUnit '1' with context 'type foo = 1'" in {
    val typeVars = collection.immutable.Map[String, TypeVar](("foo", TVConstant(PUnit)))
    val pc = ParseContext(Parser.forString("test", "foo"), typeVars = typeVars)
    val v = PType.parse(pc)
    assert(pc.pop(Tk.EOF).tk == Tk.EOF)
    assert(v.toString == "1")
    assert(v.isInstanceOf[PUnit.type], s"wrong result: expected PUnit, got ${v.getClass.getName}")
  }
  "PType.parse('foo(b)') should return PUnit 'μI ⊃ (() ⇒ 0) ⇒ b' with context 'type foo(a) = μI ⊃ (() ⇒ 0) ⇒ a'" in {
    val indexVariable = new IVBound("a", SNat)
    val itp = PType.parse(ParseContext(Parser.forString("test", "μI ⊃ (() ⇒ 0) ⇒ a")) + indexVariable).asInstanceOf[PInductive]
    val typeVars = collection.immutable.Map[String, TypeVar](("foo", TVInductive(indexVariable, itp)))
    val pc = ParseContext(Parser.forString("test", "foo(b)"), typeVars = typeVars) + new IVBound("b", SNat)
    val v = PType.parse(pc)
    assert(pc.pop(Tk.EOF).tk == Tk.EOF)
    assert(removeVarSuffixes(v.toString) == "μI ⊃ (() ⇒ 0) ⇒ b")
    assert(v.isInstanceOf[PInductive], s"wrong result: expected PInductive, got ${v.getClass.getName}")
  }
  raise(PType, "foo", "type variable is not bound")
  "PType.parse('μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ b') should return PUnit 'μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a)) ⇒ b' with context 'alg ixnat = (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a))'" in {
    val ixnat = Algebra.parse(ParseContext(Parser.forString("test", "(inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a))")))
    val algebraVars = collection.immutable.Map[String, Algebra](("ixnat", ixnat))
    val pc = ParseContext(Parser.forString("test", "μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ b"), algebras = algebraVars) + new IVBound("b", SNat)
    val v = PType.parse(pc)
    assert(pc.pop(Tk.EOF).tk == Tk.EOF)
    assert(removeVarSuffixes(v.toString) == "μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (a, ()) ⇒ (1 + a)) ⇒ b")
    assert(v.isInstanceOf[PInductive], s"wrong result: expected PInductive, got ${v.getClass.getName}")
  }
  raise(Algebra, "foo", "algebra variable is not bound")
}
