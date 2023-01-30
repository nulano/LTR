
sealed trait Index
sealed trait Proposition extends Index

object Index extends Parseable[Index] {
  override def parse(pc: ParseContext): Index = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var if tok.text == "T" => IPTrue()
      case Tk.Var if tok.text == "F" => IPFalse()
      case Tk.Var => IVariable(tok.text)
      case Tk.Number => IConstant(tok.text.toInt)
      case Tk.PLeft => ILeft(Index.parse(pc))
      case Tk.PRight => IRight(Index.parse(pc))
      case Tk.Not => IPNot(Proposition.parse(pc))
      case Tk.LParen =>
        val left = Index.parse(pc)
        val op = pc.pop(Tk.Plus, Tk.Minus, Tk.Comma, Tk.Eq, Tk.Leq, Tk.And, Tk.Or).tk
        val right = Index.parse(pc)
        pc.pop(Tk.RParen)
        op match {
          case Tk.Plus => ISum(left, right)
          case Tk.Minus => IDifference(left, right)
          case Tk.Comma => IPair(left, right)
          case Tk.Eq => IPEqual(left, right)
          case Tk.Leq => IPLessEqual(left, right)
          case Tk.And | Tk.Or =>
            (left, right) match {
              case (lp: Proposition, rp: Proposition) =>
                if op == Tk.And then IPAnd(lp, rp) else IPOr(lp, rp)
              case _ => throw ParseException("not a proposition")
            }
          case _ => throw AssertionError("unreachable")
        }
      case _ => throw UnexpectedTokenParseException(tok, "an index term")
    }
  }
}

object Proposition extends Parseable[Proposition] {
  override def parse(pc: ParseContext): Proposition =
    Index.parse(pc) match
      case proposition: Proposition => proposition
      case _ => throw ParseException("not a proposition")
}

case class IVariable(name: String) extends Index {
  override def toString: String = name
}
case class IConstant(value: Int) extends Index {
  override def toString: String = s"$value"
}
case class ISum(left: Index, right: Index) extends Index {
  override def toString: String = s"($left + $right)"
}
case class IDifference(left: Index, right: Index) extends Index {
  override def toString: String = s"($left - $right)"
}
case class IPair(left: Index, right: Index) extends Index {
  override def toString: String = s"($left, $right)"
}
case class ILeft(value: Index) extends Index {
  override def toString: String = s"π₁ $value"
}
case class IRight(value: Index) extends Index {
  override def toString: String = s"π₂ $value"
}
case class IPEqual(left: Index, right: Index) extends Proposition {
  override def toString: String = s"($left = $right)"
}
case class IPLessEqual(left: Index, right: Index) extends Proposition {
  override def toString: String = s"($left ≤ $right)"
}
case class IPAnd(left: Proposition, right: Proposition) extends Proposition {
  override def toString: String = s"($left ∧ $right)"
}
case class IPOr(left: Proposition, right: Proposition) extends Proposition {
  override def toString: String = s"($left ∨ $right)"
}
case class IPNot(prop: Proposition) extends Proposition {
  override def toString: String = s"¬$prop"
}
case class IPTrue() extends Proposition {
  override def toString: String = "T"
}
case class IPFalse() extends Proposition {
  override def toString: String = "F"
}
