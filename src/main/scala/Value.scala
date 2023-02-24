
type VariableContext = Map[String, PType]

sealed trait Value

object Value extends Parseable[Value] {
  def parse(pc: ParseContext): Value = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var => ValVariable(tok.text)(tok)
      case Tk.LAngle => {
        if pc.peek().tk == Tk.RAngle then {
          pc.pop(Tk.RAngle)
          ValUnit()(tok)
        } else {
          val left = Value.parse(pc)
          pc.pop(Tk.Comma)
          val right = Value.parse(pc)
          pc.pop(Tk.RAngle)
          ValPair(left, right)(tok)
        }
      }
      case Tk.Inl => ValLeft(Value.parse(pc))(tok)
      case Tk.Inr => ValRight(Value.parse(pc))(tok)
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val v = Value.parse(pc)
        pc.pop(Tk.RParen)
        ValInto(v)(tok)
      }
      case Tk.LBrace => {
        val exp = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        ValExpression(exp)(tok)
      }
      case _ => throw UnexpectedTokenParseException(tok, "a value")
    }
  }

  /**
   * Check value matches tp, i.e. `Θ; Δ; Γ ⊢ value ⇐ tp / Χ ⊣ Δ'` (fig. 66a)
   * @param value the value to check
   * @param tp the type to check
   * @param ctx the index variable context, i.e. Θ; Δ
   * @param vars the variable context, i.e. Γ
   * @return the output constraints, i.e. Χ
   */
  def checkType(value: Value, tp: PType)(ctx: IndexVariableCtx, vars: VariableContext): List[TypingConstraint] = {
    (value, tp) match {
      // Alg⇐∃
      case (_, PExists(v, t)) =>
        val temp = new IVAlgorithmic(v)
        val out = checkType(value, (IVariable(temp) / v)(t))(ctx + temp, vars)
        if temp.solution.isEmpty then
          throw TypeException(s"failed to determine algorithmic variable $temp")
        out
      // Alg⇐∧
      case (_, PProperty(t, p)) =>
        val out = checkType(value, t)(ctx, vars)
        p match {
          // Inst
          case IPEqual(IVariable(rav: IVAlgorithmic), rv) if rav.solution.isEmpty =>
            val rvn = rv.norm
            try
              val ls = rvn.sort(iv => !iv.isInstanceOf[IVAlgorithmic]) // TODO ctx.filter(...)
              if ls == rav.sort then
                rav.solution = Some(rvn)
            catch
              case _: SortException => ()
          case _ => ()
        }
        SCProposition(p) +: out
      // Alg⇐Var
      case (ValVariable(v), _) =>
        val t = vars(v)
        List(PType.subtype(t, tp)(ctx))
      // Alg⇐1
      case (ValUnit(), PUnit) => List.empty
      // Alg⇐×
      case (ValPair(vl, vr), PProd(tl, tr)) =>
        checkType(vl, tl)(ctx, vars) ++ checkType(vr, tr)(ctx, vars)
      // Alg⇐+₁
      case (ValLeft(v), PSum(tl, _)) => checkType(v, tl)(ctx, vars)
      // Alg⇐+₂
      case (ValRight(v), PSum(_, tr)) => checkType(v, tr)(ctx, vars)
      // Alg⇐μ
      case (ValInto(v), t: PInductive) => checkType(v, t.unroll)(ctx, vars)
      // Alg⇐↓
      case (ValExpression(e), PSuspended(n)) => List(TCExpression(e, n))
      case _ => throw TypeException(s"value does not match required type: $value ⇐ $tp")
    }
  }
}

case class ValVariable(variable: String)(val token: Token) extends Value {
  override def toString: String = variable
}
case class ValUnit()(val token: Token) extends Value {
  override def toString: String = "<>"
}
case class ValPair(left: Value, right: Value)(val token: Token) extends Value {
  override def toString: String = s"<$left, $right>"
}
case class ValLeft(value: Value)(val token: Token) extends Value {
  override def toString: String = s"inl $value"
}
case class ValRight(value: Value)(val token: Token) extends Value {
  override def toString: String = s"inr $value"
}
case class ValInto(value: Value)(val token: Token) extends Value {
  override def toString: String = s"into($value)"
}
case class ValExpression(expression: Expression)(val token: Token) extends Value {
  override def toString: String = s"{$expression}"
}
