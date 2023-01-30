object Main {
  def runTest(s: String): Unit = {
    println(s"Testing $s")
    val pc = StringParseContext(s)
    val v = BoundExpression.parse(pc)
    val s2 = v.toString
    println(s2)
    val v2 = BoundExpression.parse(StringParseContext(s2))
    println(s"Normalized equals original: ${v equals v2}")
    println(s"Result type: ${v.getType(VariableContext(List())).result}")
    println()
  }

  def main(args: Array[String]): Unit = {
    /*
    <<>, inl  { return { fun x . return <> } }   >
    :
    (1) × ((V ^ V (?) -> (^ 1) ) + (?))
    */
    runTest("(return <<>, inl  { return { fun x . return < > } }> : ^(1 × (V ^ V (1 ~ ^ 1 ) + 0)  ))")

    // [succ : ↑∀a : ℕ . Nat(a) → ↑Nat(1 + a)](0)
    // TODO erasure: runTest("[{λx . return into(inj₂ <x, <>>)} : ↓∀a : ℕ . (μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ a → ↑μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ (1 + a))](into(inj₁ <>))")
    runTest("[{λx . return into(inj₂ <x, <>>)} : ↓(μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (b, ()) ⇒ (1 + b)) ⇒ a → ↑μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (b, ()) ⇒ (1 + b)) ⇒ (1 + a))](into(inj₁ <>))")

    // [pred : ↑∀a : ℕ . Nat(a) → ↑Nat(a - 1)](1)
    // TODO match syntax sugar: runTest("[{λx . match x {into(inj₁ <>) ⇒ return x ‖ into(inj₂ <y, <>>) ⇒ return y}} : ↓∀a : ℕ . (μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ a → ↑μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ (a - 1))](into(inj₂ <into(inj₁ <>>), <>))")
    // TODO erasure: runTest("[{λx . match x {into(y) ⇒ match y {inj₁ _ ⇒ return x ‖ inj₂ z ⇒ match z {<w, _> ⇒ return w}}}} : ↓∀a : ℕ . (μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ a → ↑μ(I ⊕ (Id ⊗ I)) ⊃ ixnat ⇒ (a - 1))](into(inj₂ <into(inj₁ <>), <>>))")
    runTest("[{λx . match x {into(y) ⇒ match y {inj₁ u ⇒ return x ‖ inj₂ z ⇒ match z {<w, u> ⇒ return w}}}} : ↓(μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (b, ()) ⇒ (1 + b)) ⇒ a → ↑μ(I ⊕ (Id ⊗ I)) ⊃ (inl () ⇒ 0 ‖ inr (b, ()) ⇒ (1 + b)) ⇒ (a - 1))](into(inj₂ <into(inj₁ <>), <>>))")
  }
}