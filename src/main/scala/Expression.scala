
sealed trait Expression

object Expression extends Parseable[Expression] {
  override def parse(pc: ParseContext): Expression = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Return => ExpReturn(tok, Value.parse(pc))
      case Tk.Let => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Eq)
        val bound = BoundExpression.parse(pc)
        pc.pop(Tk.Semicolon)
        val body = Expression.parse(pc)
        ExpLet(tok, variable, bound, body)
      }
      // TODO Tk.Match
      case Tk.Lambda => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpFunction(tok, variable, body)
      }
      case Tk.Rec => {
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val tp = new PType {} // TODO
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpRecursive(tok, variable, tp, body)
      }
      case _ => throw ParseException("not an expression: " + tok)
    }
  }
}

case class ExpReturn(tk: Token, value: Value) extends Expression {
  override def toString: String = s"return $value"
}
case class ExpLet(tk: Token, variable: String, value: BoundExpression, body: Expression) extends Expression {
  override def toString: String = s"let $variable = $value; $body"
}
// TODO case class ExpMatch(tk: Token, ) {}
case class ExpFunction(tk: Token, variable: String, body: Expression) extends Expression {
  override def toString: String = s"λ$variable . $body"
}
case class ExpRecursive(tk: Token, variable: String, tp: PType, body: Expression) extends Expression {
  override def toString: String = s"rec $variable : $tp . $body"
}

sealed trait Head

object Head extends Parseable[Head] {
  override def parse(pc: ParseContext): Head = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var => HeadVariable(tok, tok.text)
      case Tk.LSquare => {
        val v = Value.parse(pc)
        pc.pop(Tk.Colon)
        // TODO val t = PType.parse(pc)
        pc.pop(Tk.RSquare)
        HeadValue(tok, v, PType())
      }
      case _ => throw ParseException(s"not a head: $tok")
    }
  }
}

case class HeadVariable(tok: Token, variable: String) extends Head {
  override def toString: String = variable
}
case class HeadValue(tok: Token, value: Value, tp: PType) extends Head {
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
      // TODO val tp = PType.parse(pc)
      pc.pop(Tk.RParen)
      BEExpression(tok, exp, PType())
    } else {
      val head = Head.parse(pc)
      pc.pop(Tk.LParen)
      val spine = collection.mutable.ArrayBuilder.make[Value]
      while pc.peek().tk != Tk.RParen do {
        val v = Value.parse(pc)
        pc.pop(Tk.Comma)
        spine += v
      }
      pc.pop(Tk.RParen)
      BEApplication(tok, head, spine.result())
    }
  }
}

case class BEApplication(tok: Token, head: Head, spine: Array[Value]) extends BoundExpression {
  override def toString: String = s"$head(${spine.mkString(",")})"
}
case class BEExpression(tok: Token, exp: Expression, tp: PType) extends BoundExpression {
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
          PUnit(tok)
        } else {
          val left = pc.pop(Tk.Var).text
          pc.pop(Tk.Comma)
          val right = pc.pop(Tk.Var).text
          pc.pop(Tk.RAngle)
          PPair(tok, left, right)
        }
      }
      case Tk.Inl => PInl(tok, pc.pop(Tk.Var).text)
      case Tk.Inr => PInr(tok, pc.pop(Tk.Var).text)
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        PInto(tok, variable)
      }
      case _ => throw ParseException(s"not a pattern: $tok")
    }
  }
}

case class PInto(token: Token, variable: String) extends Pattern {
  override def toString: String = s"into($variable)"
}
case class PUnit(token: Token) extends Pattern {
  override def toString: String = "<>"
}
case class PPair(token: Token, left: String, right: String) extends Pattern {
  override def toString: String = s"<$left, $right>"
}
case class PInl(token: Token, left: String) extends Pattern {
  override def toString: String = s"inl $left"
}
case class PInr(token: Token, right: String) extends Pattern {
  override def toString: String = s"inr $right"
}


