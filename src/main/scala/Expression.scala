
sealed trait Expression

object Expression extends Parseable[Expression] {
  override def parse(pc: ParseContext): Expression = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Return => ExpReturn(Value.parse(pc))(tok)
      case Tk.Let => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Eq)
        val bound = BoundExpression.parse(pc)
        pc.pop(Tk.Semicolon)
        val body = Expression.parse(pc)
        ExpLet(variable, bound, body)(tok)
      }
      // TODO Tk.Match
      case Tk.Lambda => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpFunction(variable, body)(tok)
      }
      case Tk.Rec => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val tp = NType.parse(pc)
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpRecursive(variable, tp, body)(tok)
      }
      case _ => throw ParseException("not an expression: " + tok)
    }
  }
}

case class ExpReturn(value: Value)(val token: Token) extends Expression {
  override def toString: String = s"return $value"
}
case class ExpLet(variable: String, value: BoundExpression, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"let $variable = $value; $body"
}
// TODO case class ExpMatch(tk: Token, ) {}
case class ExpFunction(variable: String, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"λ$variable . $body"
}
case class ExpRecursive(variable: String, tp: NType, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"rec $variable : $tp . $body"
}

sealed trait Head

object Head extends Parseable[Head] {
  override def parse(pc: ParseContext): Head = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var => HeadVariable(tok.text)(tok)
      case Tk.LSquare => {
        val v = Value.parse(pc)
        pc.pop(Tk.Colon)
        val tp = PType.parse(pc)
        pc.pop(Tk.RSquare)
        HeadValue(v, tp)(tok)
      }
      case _ => throw ParseException(s"not a head: $tok")
    }
  }
}

case class HeadVariable(variable: String)(val token: Token) extends Head {
  override def toString: String = variable
}
case class HeadValue(value: Value, tp: PType)(val token: Token) extends Head {
  override def toString: String = s"[$value : $tp]"
}

sealed trait BoundExpression

object BoundExpression extends Parseable[BoundExpression] {
  override def parse(pc: ParseContext): BoundExpression = {
    val tok = pc.peek()
    if tok.tk == Tk.LParen then {
      pc.pop(Tk.LParen)
      val exp = Expression.parse(pc)
      pc.pop(Tk.Colon)
      pc.pop(Tk.Up)
      val tp = PType.parse(pc)
      pc.pop(Tk.RParen)
      BEExpression(exp, tp)(tok)
    } else {
      val head = Head.parse(pc)
      pc.pop(Tk.LParen)
      val spine = new collection.immutable.VectorBuilder[Value]()
      while pc.peek().tk != Tk.RParen do {
        val v = Value.parse(pc)
        pc.pop(Tk.Comma)
        spine += v
      }
      pc.pop(Tk.RParen)
      BEApplication(head, spine.result())(tok)
    }
  }
}

case class BEApplication(head: Head, spine: Vector[Value])(val token: Token) extends BoundExpression {
  override def toString: String = s"$head(${spine.mkString(",")})"
}
case class BEExpression(exp: Expression, tp: PType)(val token: Token) extends BoundExpression {
  override def toString: String = s"($exp : ↑$tp)"
}

sealed trait Pattern

object Pattern extends Parseable[Pattern] {
  override def parse(pc: ParseContext): Pattern = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.LAngle => {
        if pc.peek().tk == Tk.RAngle then {
          pc.pop(Tk.RAngle)
          PatUnit()(tok)
        } else {
          val left = pc.pop(Tk.Var).text
          pc.pop(Tk.Comma)
          val right = pc.pop(Tk.Var).text
          pc.pop(Tk.RAngle)
          PatPair(left, right)(tok)
        }
      }
      case Tk.Inl => PatInl(pc.pop(Tk.Var).text)(tok)
      case Tk.Inr => PatInr(pc.pop(Tk.Var).text)(tok)
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        PatInto(variable)(tok)
      }
      case _ => throw ParseException(s"not a pattern: $tok")
    }
  }
}

case class PatInto(variable: String)(val token: Token) extends Pattern {
  override def toString: String = s"into($variable)"
}
case class PatUnit()(val token: Token) extends Pattern {
  override def toString: String = "<>"
}
case class PatPair(left: String, right: String)(val token: Token) extends Pattern {
  override def toString: String = s"<$left, $right>"
}
case class PatInl(left: String)(val token: Token) extends Pattern {
  override def toString: String = s"inl $left"
}
case class PatInr(right: String)(val token: Token) extends Pattern {
  override def toString: String = s"inr $right"
}


