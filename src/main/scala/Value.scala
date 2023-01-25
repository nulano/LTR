
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
      case _ => throw ParseException("not a value: " + tok.tk)
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
