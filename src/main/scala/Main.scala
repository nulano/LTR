object Main {

  def main(args: Array[String]): Unit = {
    val input =
      """
        |let test = (return <<>, inl { return { fun x . return < > } }> : ^(1 × (V ^ V (1 ~ ^ 1 ) + 0)  ))
        |
        |type unit = 1
        |alg ixnat = (inl () => 0 || inr (a, ()) => (1 + a))
        |type nat(b:N) = fix (I (+) (Id (X) I)) S ixnat => b
        |let unit = (return <> : ^unit)
        |let zero = (return into(inl unit) : ^nat(0))
        |
        |def succ : ∀b : ℕ .
        |           (nat(b) → ↑nat((1 + b)))
        |         = λx . return into(inj₂ <x, <>>)
        |let one = succ(zero)
        |let two = succ(one)
        |
        |def succe : ∀b : ℕ .
        |            (nat(b) → ↑∃c : ℕ . (nat(c) ∧ [(c = (b + 1))]))
        |          = λx . let y = succ(x); return y
        |let onee = succe(zero)
        |let twoe = succe(onee)
        |let two_test = (let i = succe(zero); let j = succe(i); return j : ↑nat(2))  -- demonstrated error in extraction, TODO test
        |
        |def pred : ∀b : ℕ . [(b > 0)] ⊃
        |           (nat(b) → ↑nat((b - 1)))
        |         = λx . match x {
        |                  into(y) ⇒ match y {
        |                    inj₁ u ⇒ unreachable
        |                  ‖ inj₂ z ⇒ match z {
        |                               <w, u> ⇒ return w
        |                             }
        |                  }
        |                }
        |let one_again = pred(two)
        |
        |def pred_with_clamp : ∀b : ℕ . (nat(b) → ↑nat((b - 1)))
        |                    = λx . match x {
        |                  into(y) ⇒ match y {
        |                    inj₁ u ⇒ return x
        |                  ‖ inj₂ z ⇒ match z {
        |                               <w, u> ⇒ return w
        |                             }
        |                  }
        |                }
        |let zero_again = pred_with_clamp(zero)
        |def hide_index : ∀b : ℕ . (nat(b) → ↑∃c : ℕ . (nat(c) ∧ [(b = c)]))
        |               = λx . return x
        |let zeroh = hide_index(zero_again)
        |
        |def add_two : ∀b : ℕ .
        |              (nat(b) → ↑nat((2 + b)))
        |            = λx . let y = succ(x); let z = succ(y); return z
        |let two_again = add_two(zero)
        |
        |rec sum : ∀b : ℕ . ∀c : ℕ .
        |          (nat(b) → (nat(c) → ↑nat((b + c))))
        |        = λx . λy . match x {
        |            into(xx) ⇒ match xx {
        |              inj₁ u ⇒ return y
        |            ‖ inj₂ x_minus_one_and_unit ⇒ match x_minus_one_and_unit {
        |                <x_minus_one, u> ⇒
        |                  let recv = sum(x_minus_one, y);
        |                  let out = succ(recv);
        |                  return out
        |              }
        |            }
        |          }
        |let four = sum(two, two_again)
        |
        |def double : ∀b : ℕ . (nat(b) → ↑nat((b + b))) = λx . let y = sum(x, x); return y
        |let eight = double(four)
        |
        |def erase : ∀b : ℕ . (nat(b) → ↑∃c : ℕ . nat(c)) = λx . return x
        |let zeroer = erase(zero)
        |let doubled = double(zeroer)
        |
        |rec sub : ∀b : ℕ . ∀c : ℕ . [(b ≤ c)] ⊃
        |          (nat(b) → (nat(c) → ↑nat((c - b))))
        |        = λx . λy . match x {
        |            into(xx) ⇒ match xx {
        |              inj₁ u ⇒ return y
        |            ‖ inj₂ x_minus_one_and_unit ⇒ match x_minus_one_and_unit {
        |                <x_minus_one, u> ⇒
        |                  let y_minus_one = pred(y);
        |                  let out = sub(x_minus_one, y_minus_one);
        |                  return out
        |              }
        |            }
        |          }
        |let six = sub(two, eight)
        |""".stripMargin

    val repl = new REPL()
    val reader = input.split('\n').iterator ++ StdInReader
    val parser = new Parser("<stdin>", reader)
    while parser.peek().tk != Tk.EOF do {
      try
        val cmd = REPLCommand.parse(repl.makeParseContext(parser))
        println(repl.processCommand(cmd))
      catch
        case parseException: ParseException =>
          parseException.printStackTrace()
          parser.skipLine()
        case typeException: TypeException =>
          typeException.printStackTrace()
    }
  }
}

object StdInReader extends Iterator[String] {
  override def hasNext: Boolean = true

  override def next(): String = {
    val line = scala.io.StdIn.readLine
    if line == null then
      throw new NoSuchElementException()
    else line
  }
}
