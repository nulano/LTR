
sealed trait Value {
  def checkType(vc: VariableContext, tp: PType): Unit
}

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
}

case class ValVariable(variable: String)(val token: Token) extends Value {
  override def toString: String = variable

  // Unref <= Var
  override def checkType(vc: VariableContext, tp: PType): Unit =
    if !vc.check(variable, tp) then throw TypeException(s"variable $variable does not have required type $tp")
}
case class ValUnit()(val token: Token) extends Value {
  override def toString: String = "<>"

  // Unref <= 1
  override def checkType(vc: VariableContext, tp: PType): Unit = tp match {
    case PUnit() => ()
    case _ => throw TypeException(s"$this does not have required type $tp")
  }
}
case class ValPair(left: Value, right: Value)(val token: Token) extends Value {
  override def toString: String = s"<$left, $right>"

  // Unref <= ×
  override def checkType(vc: VariableContext, tp: PType): Unit = tp match {
    case PProd(l, r) => left.checkType(vc, l); right.checkType(vc, r)
    case _ => throw TypeException(s"$this does not have required type $tp")
  }
}
case class ValLeft(value: Value)(val token: Token) extends Value {
  override def toString: String = s"inl $value"

  // Unref <= +_1
  override def checkType(vc: VariableContext, tp: PType): Unit = tp match {
    case PSum(l, _) => value.checkType(vc, l)
    case _ => throw TypeException(s"$this does not have required type $tp")
  }
}
case class ValRight(value: Value)(val token: Token) extends Value {
  override def toString: String = s"inr $value"

  // Unref <= +_2
  override def checkType(vc: VariableContext, tp: PType): Unit = tp match {
    case PSum(_, r) => value.checkType(vc, r)
    case _ => throw TypeException(s"$this does not have required type $tp")
  }
}
case class ValInto(value: Value)(val token: Token) extends Value {
  override def toString: String = s"into($value)"

  override def checkType(vc: VariableContext, tp: PType): Unit = throw TypeException("TODO") // TODO
}
case class ValExpression(expression: Expression)(val token: Token) extends Value {
  override def toString: String = s"{$expression}"

  override def checkType(vc: VariableContext, tp: PType): Unit = tp match {
    case PSuspended(t) => expression.checkType(vc, t)
    case _ => throw TypeException(s"$this does not have required type $tp")
  }
}
