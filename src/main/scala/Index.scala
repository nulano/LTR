
sealed trait Index {
  def substitute(variable: String, value: Index): Index
}
sealed trait Proposition extends Index {
  override def substitute(variable: String, value: Index): Proposition
}

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

  override def substitute(variable: String, value: Index): Index = 
    if name == variable then value else this
}
case class IConstant(value: Int) extends Index {
  override def toString: String = s"$value"

  override def substitute(variable: String, value: Index): Index = this
}
case class ISum(left: Index, right: Index) extends Index {
  override def toString: String = s"($left + $right)"

  override def substitute(variable: String, value: Index): Index =
    ISum(left.substitute(variable, value), right.substitute(variable, value))
}
case class IDifference(left: Index, right: Index) extends Index {
  override def toString: String = s"($left - $right)"

  override def substitute(variable: String, value: Index): Index =
    IDifference(left.substitute(variable, value), right.substitute(variable, value))
}
case class IPair(left: Index, right: Index) extends Index {
  override def toString: String = s"($left, $right)"

  override def substitute(variable: String, value: Index): Index =
    IPair(left.substitute(variable, value), right.substitute(variable, value))
}
case class ILeft(value: Index) extends Index {
  override def toString: String = s"π₁ $value"

  override def substitute(variable: String, value: Index): Index =
    ILeft(value.substitute(variable, value))
}
case class IRight(value: Index) extends Index {
  override def toString: String = s"π₂ $value"

  override def substitute(variable: String, value: Index): Index =
    IRight(value.substitute(variable, value))
}
case class IPEqual(left: Index, right: Index) extends Proposition {
  override def toString: String = s"($left = $right)"

  override def substitute(variable: String, value: Index): Proposition =
    IPEqual(left.substitute(variable, value), right.substitute(variable, value))
}
case class IPLessEqual(left: Index, right: Index) extends Proposition {
  override def toString: String = s"($left ≤ $right)"

  override def substitute(variable: String, value: Index): Proposition =
    IPLessEqual(left.substitute(variable, value), right.substitute(variable, value))
}
case class IPAnd(left: Proposition, right: Proposition) extends Proposition {
  override def toString: String = s"($left ∧ $right)"

  override def substitute(variable: String, value: Index): Proposition =
    IPAnd(left.substitute(variable, value), right.substitute(variable, value))
}
case class IPOr(left: Proposition, right: Proposition) extends Proposition {
  override def toString: String = s"($left ∨ $right)"

  override def substitute(variable: String, value: Index): Proposition =
    IPOr(left.substitute(variable, value), right.substitute(variable, value))
}
case class IPNot(prop: Proposition) extends Proposition {
  override def toString: String = s"¬$prop"

  override def substitute(variable: String, value: Index): Proposition =
    IPNot(prop.substitute(variable, value))
}
case class IPTrue() extends Proposition {
  override def toString: String = "T"

  override def substitute(variable: String, value: Index): Proposition = this
}
case class IPFalse() extends Proposition {
  override def toString: String = "F"

  override def substitute(variable: String, value: Index): Proposition = this
}
