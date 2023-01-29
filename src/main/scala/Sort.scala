sealed trait Sort

object Sort extends Parseable[Sort] {
  override def parse(pc: ParseContext): Sort = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Boolean => SBool()
      case Tk.Natural => SNat()
      case Tk.Integer => SInt()
      case Tk.LParen =>
        val left = Sort.parse(pc)
        pc.pop(Tk.Times)
        val right = Sort.parse(pc)
        pc.pop(Tk.RParen)
        SProd(left, right)
      case _ => throw UnexpectedTokenParseException(tok, "a sort")
    }
  }
}

case class SBool() extends Sort {
  override def toString: String = "𝔹"
}
case class SNat() extends Sort {
  override def toString: String = "ℕ"
}
case class SInt() extends Sort {
  override def toString: String = "ℤ"
}
case class SProd(left: Sort, right: Sort) extends Sort {
  override def toString: String = s"($left × $right)"
}

