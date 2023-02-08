import org.scalatest.freespec.AnyFreeSpec

import scala.annotation.targetName
import scala.language.implicitConversions

//noinspection NonAsciiCharacters
class IndexSortTest extends AnyFreeSpec {

  private case class TestCase(string: String, sort: Sort)

  private case class TestCaseErr(string: String, msg: String)

  //noinspection NoTargetNameAnnotationForOperatorLikeDefinition
  private implicit class TestSort(sort: Sort) {
    inline infix def ::(string: String): TestCase = TestCase(string, sort)
  }

  //noinspection NoTargetNameAnnotationForOperatorLikeDefinition
  private implicit class TestMsg(msg: String) {
    inline infix def ::(string: String): TestCaseErr = TestCaseErr(string, msg)
  }

  //noinspection NoTargetNameAnnotationForOperatorLikeDefinition
  private implicit class TestCtx(ctx: Set[String]) {
    private val indexVars: Set[IndexVariable] =
      ctx.map(s => IVBound.parse(ParseContext(Parser("test-setup", List(s).iterator))))

    private val ctxString = (List("∙") ++ indexVars.map(i => s"${i.name} : ${i.sort}")).mkString(", ")

    inline infix def |-(test: TestCase): Unit = {
      val string = test.string
      val sort = test.sort
      val indexVarMap = indexVars.map(i => (i.name, i)).toMap
      s"$ctxString ⊢ $string : $sort" in {
        val pc = ParseContext(Parser.forString("test", string), indexVars = indexVarMap)
        val v = Index.parse(pc)
        assert(v.toString == string)
        val s = v.sort(indexVars)
        assert(s == sort)
        if (indexVars.nonEmpty) {
          val ex = intercept[TypeException] { v.sort(Set.empty) }
          assert(ex.msg == "variable not in context")
        }
      }
    }

    inline infix def |/-(test: TestCaseErr): Unit = {
      val string = test.string
      val msg = test.msg
      val indexVarMap = indexVars.map(i => (i.name, i)).toMap
      s"$ctxString ⊬ $string : τ, raises '$msg'" in {
        val pc = ParseContext(Parser.forString("test", string), indexVars = indexVarMap)
        val v = Index.parse(pc)
        assert(v.toString == string)
        val ex = intercept[TypeException] { v.sort(indexVars) }
        assert(ex.msg == msg)
      }
    }
  }

  // AlgIxVar
  Set("foo : ℕ") |- "foo" :: SNat

  // AlgIxConst
  Set.empty |- "T" :: SBool
  Set.empty |- "F" :: SBool
  Set.empty |- "42" :: SNat
  Set.empty |- "+42" :: SInt
  Set.empty |- "-42" :: SInt

  // AlgIxAdd
  Set("a : ℕ", "b : ℕ") |- "(a + b)" :: SNat
  Set("a : ℤ", "b : ℤ") |- "(a + b)" :: SInt
  Set("a : ℕ", "b : ℤ") |/- "(a + b)" :: "sort mismatch: ℕ + ℤ"
  Set("a : ℤ", "b : ℕ") |/- "(a + b)" :: "sort mismatch: ℤ + ℕ"
  Set("a : 𝔹", "b : 𝔹") |/- "(a + b)" :: "can't perform addition on 𝔹"

  // AlgIxSubtract
  Set("a : ℕ", "b : ℕ") |- "(a - b)" :: SNat
  Set("a : ℤ", "b : ℤ") |- "(a - b)" :: SInt
  Set("a : ℕ", "b : ℤ") |/- "(a - b)" :: "sort mismatch: ℕ - ℤ"
  Set("a : ℤ", "b : ℕ") |/- "(a - b)" :: "sort mismatch: ℤ - ℕ"
  Set("a : 𝔹", "b : 𝔹") |/- "(a - b)" :: "can't perform subtraction on 𝔹"

  // AlgIxProd
  Set("a : ℕ", "b : ℤ") |- "(a, b)" :: SProd(SNat, SInt)

  // AlgIxProj{1,2}
  Set("p : (ℕ × ℤ)") |- "π₁ p" :: SNat
  Set("p : (ℕ × ℤ)") |- "π₂ p" :: SInt
  Set("p : 𝔹") |/- "π₁ p" :: "can't perform projection on 𝔹"
  Set("p : ℕ") |/- "π₂ p" :: "can't perform projection on ℕ"

  // AlgIx=
  Set("a : ℕ", "b : ℕ") |- "(a = b)" :: SBool
  Set("a : ℤ", "b : ℤ") |- "(a = b)" :: SBool
  Set("a : 𝔹", "b : 𝔹") |- "(a = b)" :: SBool
  Set("a : ℕ", "b : ℤ") |/- "(a = b)" :: "sort mismatch: ℕ = ℤ"
  Set("a : ℤ", "b : ℕ") |/- "(a = b)" :: "sort mismatch: ℤ = ℕ"
  Set("a : (𝔹 × ℤ)", "b : (𝔹 × ℤ)") |- "(a = b)" :: SBool
  Set("a : (𝔹 × ℤ)", "b : (𝔹 × ℕ)") |/- "(a = b)" :: "sort mismatch: (𝔹 × ℤ) = (𝔹 × ℕ)"

  // AlgIx≤
  Set("a : ℕ", "b : ℕ") |- "(a ≤ b)" :: SBool
  Set("a : ℤ", "b : ℤ") |- "(a ≤ b)" :: SBool
  Set("a : ℕ", "b : ℤ") |/- "(a ≤ b)" :: "sort mismatch: ℕ ≤ ℤ"
  Set("a : ℤ", "b : ℕ") |/- "(a ≤ b)" :: "sort mismatch: ℤ ≤ ℕ"
  Set("a : 𝔹", "b : 𝔹") |/- "(a ≤ b)" :: "can't perform comparison on 𝔹"
  Set("a : (𝔹 × ℤ)", "b : (𝔹 × ℤ)") |/- "(a ≤ b)" :: "can't perform comparison on (𝔹 × ℤ)"

  // AlgIx{∧,∨,¬}
  Set("a : ℕ", "b : ℕ") |- "¬(a = b)" :: SBool
  Set("a : ℕ", "b : ℕ") |- "(T ∧ (a = b))" :: SBool
  Set("a : ℕ", "b : ℕ") |- "(T ∨ (a = b))" :: SBool
  Set("a : ℕ", "b : ℕ") |- "((a = b) ∧ T)" :: SBool
  Set("a : ℕ", "b : ℕ") |- "((a = b) ∨ T)" :: SBool
}
