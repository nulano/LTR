import org.scalatest.freespec.AnyFreeSpec

class TypeTest extends AnyFreeSpec {
  //noinspection NoTargetNameAnnotationForOperatorLikeDefinition
  private implicit class TestCtx(ctx: Set[String]) {
    private val indexVars: Set[IndexVariable] =
      ctx.map(s => IVBound.parse(ParseContext(Parser("test-setup", List(s).iterator))))

    private val indexVarsString = (List("∙") ++ indexVars.map(i => s"${i.name} : ${i.sort}")).mkString(", ")

    inline infix def |-(test: TestCase): Unit = {
      val indexVarMap = indexVars.map(i => (i.name, i)).toMap
      val string = test.string
      val expected = test.expectedNames.map(indexVarMap)
      val expectedString = (List("∙") ++ expected.map(i => s"${i.name} : ${i.sort}")).mkString(", ")

      val (obj, tp) = try
        (PType.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "ptype")
      catch
        case _: ParseException =>
          try
            (NType.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "ntype")
          catch
            case _: ParseException =>
              (Functor.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "functor")
      assert(obj.toString == string)

      s"$indexVarsString ⊢ $obj $tp[$expectedString]" in {
        val vd = obj.wellFormed(indexVars)
        assert(vd == expected)
        if (indexVars.nonEmpty) {
          val ex = intercept[TypeException] {
            obj.wellFormed(Set.empty)
          }
          assert(ex.msg == "variable not in context")
        }
      }
    }

    inline infix def |/-(test: TestCaseErr): Unit = {
      val indexVarMap = indexVars.map(i => (i.name, i)).toMap
      val string = test.string
      val msg = test.msg

      val (obj, tp) = try
        (PType.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "ptype")
      catch
        case _: ParseException =>
          try
            (NType.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "ntype")
          catch
            case _: ParseException =>
              (Functor.parse(ParseContext(Parser.forString("test", string), indexVars = indexVarMap)), "functor")
      assert(obj.toString == string)

      s"$indexVarsString ⊬ $obj $tp[Ξ], raises '$msg'" in {
        val ex = intercept[TypeException] { obj.wellFormed(indexVars) }
        assert(ex.msg == msg)
      }
    }
  }

  private case class TestCase(string: String, expectedNames: Set[String])

  private case class TestCaseErr(string: String, msg: String)

  //noinspection NoTargetNameAnnotationForOperatorLikeDefinition
  private implicit class TestStr(string: String) {
    inline infix def -->(expectedNames: Set[String]): TestCase = TestCase(string, expectedNames)

    inline infix def -->(err: String): TestCaseErr = TestCaseErr(string, err)
  }


  // AlgFunctorId
  Set.empty |- "Id" --> Set.empty

  // AlgFunctorI
  Set.empty |- "I" --> Set.empty

  // AlgTp0
  Set.empty |- "0" --> Set.empty

  // AlgTp1
  Set.empty |- "1" --> Set.empty

  // AlgTpμ, AlgAlgI
  Set("a : ℕ") |- "μI ⊃ (() ⇒ 0) ⇒ a" --> Set("a")
  Set("a : ℕ") |- "μI ⊃ (() ⇒ 0) ⇒ (a + 1)" --> Set.empty
  Set("a : ℕ") |/- "μI ⊃ (inl () ⇒ 0 ‖ inr () ⇒ 1) ⇒ a" --> "algebra is incompatible with functor: (inl () ⇒ 0 ‖ inr () ⇒ 1), I"
  // fails at the parser level
  // Set("a : ℕ") |/- "μI ⊃ (() ⇒ a) ⇒ 0" --> "variable not in context"
  // Set("a : ℕ") |/- "μI ⊃ (() ⇒ a) ⇒ a" --> "variable not in context"

  // AlgTpμ, AlgAlgConst⊗
  Set("a : ℕ", "b : ℤ") |- "μ([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ ((_, ()) ⇒ +42) ⇒ b" --> Set("a", "b")
  Set("a : ℕ", "b : ℤ") |- "μ([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ ((_, ()) ⇒ +42) ⇒ (b + -5)" --> Set("a")
  Set("a : ℕ", "b : ℤ") |/- "μ([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ (() ⇒ +42) ⇒ b" --> "algebra pattern is incompatible with functor"
  Set("b : ℤ") |/- "μ([∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ 7] ⊗ I) ⊃ ((_, ()) ⇒ +42) ⇒ b" --> "cannot determine value of existentially quantified index: ∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ 7"

  // AlgTpμ, AlgAlgConst∃⊗
  Set("b : 𝔹") |- "μ([∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ ((pack(x, _), ()) ⇒ (x = 7)) ⇒ b" --> Set("b")
  Set("b : 𝔹") |/- "μ([∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ 7] ⊗ I) ⊃ ((pack(x, _), ()) ⇒ (x = 7)) ⇒ b" --> "cannot determine value of existentially quantified index: ∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ 7"
  Set("c : ℕ") |- "μ([∃a : ℕ . ∃b : ℕ . (μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ 1) ⇒ b)] ⊗ I) ⊃ ((pack(x, pack(y, _)), ()) ⇒ (x + y)) ⇒ c" --> Set("c")
  Set("b : ℕ") |/- "μ([∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ ((r, ()) ⇒ 7) ⇒ b" --> "algebra pattern is incompatible with functor"
  Set("a : ℕ", "b : 𝔹") |/- "μ([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊃ ((pack(x, _), ()) ⇒ (x = 7)) ⇒ b" --> "algebra pattern is incompatible with functor"

  // AlgTpμ, AlgAlgId⊗
  Set("b : ℕ") |- "μ(Id ⊗ I) ⊃ ((a, ()) ⇒ (a + 4)) ⇒ b" --> Set("b")
  Set.empty |/- "μ(Id ⊗ I) ⊃ (() ⇒ 4) ⇒ 7" --> "algebra pattern is incompatible with functor"
  Set.empty |/- "μI ⊃ ((a, ()) ⇒ (a + 4)) ⇒ 7" --> "algebra pattern is incompatible with functor"

  // AlgTpπ, AlgAlg⊕
  Set("a : ℕ") |- "μ(I ⊕ I) ⊃ (inl () ⇒ 0 ‖ inr () ⇒ 1) ⇒ a" --> Set("a")
  Set("a : ℕ") |/- "μ(I ⊕ I) ⊃ (inl () ⇒ 0 ‖ inr () ⇒ +1) ⇒ a" --> "algebra result is incompatible with requirement: ℤ != ℕ"
  Set("a : ℕ") |/- "μ(I ⊕ I) ⊃ (inl () ⇒ +0 ‖ inr () ⇒ 1) ⇒ a" --> "algebra result is incompatible with requirement: ℤ != ℕ"

  // AlgFunctorConst
  Set("a : ℕ") |- "([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I)" --> Set("a")
  Set("a : ℕ") |/- "([μI ⊃ (() ⇒ +0) ⇒ a] ⊗ I)" --> "algebra result is incompatible with requirement: ℤ != ℕ"

  // AlgFunctor⊗
  Set("a : ℕ", "b : ℤ") |- "([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ ([μI ⊃ (() ⇒ +0) ⇒ b] ⊗ I))" --> Set("a", "b")

  // AlgFunctor⊕
  Set("a : ℕ", "b : ℤ") |- "(([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊕ ([μI ⊃ (() ⇒ +0) ⇒ b] ⊗ I))" --> Set.empty
  Set("a : ℕ") |- "(([μI ⊃ (() ⇒ 0) ⇒ a] ⊗ I) ⊕ ([μI ⊃ (() ⇒ 1) ⇒ a] ⊗ I))" --> Set("a")

  // AlgTp+
  Set("a : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a + μI ⊃ (() ⇒ 1) ⇒ a)" --> Set("a")
  Set("a : ℕ", "b : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a + μI ⊃ (() ⇒ 1) ⇒ b)" --> Set.empty

  // AlgTp×
  Set("a : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ 1) ⇒ a)" --> Set("a")
  Set("a : ℕ", "b : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ 1) ⇒ b)" --> Set("a", "b")

  // AlgTp∃
  Set.empty |- "∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ a" --> Set.empty
  Set("b : ℕ") |- "∃a : ℕ . (μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ 1) ⇒ b)" --> Set("b")
  Set.empty |- "∃a : ℕ . ∃b : ℤ . (μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ -1) ⇒ b)" --> Set.empty
  Set("b : ℕ") |/- "∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ b" --> "cannot determine value of existentially quantified index: ∃a : ℕ . μI ⊃ (() ⇒ 0) ⇒ b"

  // AlgTp∧
  Set("a : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a ∧ [(a = 5)])" --> Set("a")
  Set("a : ℕ") |/- "(μI ⊃ (() ⇒ 0) ⇒ a ∧ [(a ≤ +5)])" --> "sort mismatch: ℕ ≤ ℤ"

  // AlgTp↓
  Set("a : ℕ", "b : ℕ") |- "↑(μI ⊃ (() ⇒ 0) ⇒ a × μI ⊃ (() ⇒ 1) ⇒ b)" --> Set.empty

  // AlgTp→
  Set("a : ℕ") |- "(μI ⊃ (() ⇒ 0) ⇒ a → ↑1)" --> Set("a")
  Set("a : ℕ", "b : ℤ") |- "(μI ⊃ (() ⇒ 0) ⇒ a → (μI ⊃ (() ⇒ -42) ⇒ b → ↑1))" --> Set("a", "b")
  Set("b : ℤ") |- "(1 → (μI ⊃ (() ⇒ -42) ⇒ b → ↑1))" --> Set("b")

  // AlgTp↑
  Set("a : ℕ", "b : ℤ") |- "↓(μI ⊃ (() ⇒ 0) ⇒ a → (μI ⊃ (() ⇒ -42) ⇒ b → ↑1))" --> Set.empty

  // AlgTp∀
  Set("b : ℤ") |- "∀a : ℕ . (μI ⊃ (() ⇒ 0) ⇒ a → (μI ⊃ (() ⇒ -42) ⇒ b → ↑1))" --> Set("b")
  Set.empty |- "∀a : ℕ . ∀b : ℤ . (μI ⊃ (() ⇒ 0) ⇒ a → (μI ⊃ (() ⇒ -42) ⇒ b → ↑1))" --> Set.empty
  Set("b : ℤ") |/- "∀a : ℕ . (μI ⊃ (() ⇒ -42) ⇒ b → ↑1)" --> "cannot determine value of universally quantified index: ∀a : ℕ . (μI ⊃ (() ⇒ -42) ⇒ b → ↑1)"

  // AlgTp⊃
  Set("a : ℕ") |- "[(a ≤ 5)] ⊃ (μI ⊃ (() ⇒ 0) ⇒ a → ↑1)" --> Set("a")
  Set("a : ℕ") |/- "[(a ≤ +5)] ⊃ (μI ⊃ (() ⇒ 0) ⇒ a → ↑1)" --> "sort mismatch: ℕ ≤ ℤ"
}
