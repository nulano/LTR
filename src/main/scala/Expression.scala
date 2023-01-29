
sealed trait Expression {
  def checkType(vc: VariableContext, tp: NType): Unit
}

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
      case Tk.Match => {
        val head = Head.parse(pc)
        val clauses = MatchPattern.parse(pc)
        ExpMatch(head, clauses)(tok)
      }
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
      case _ => throw UnexpectedTokenParseException(tok, "an expression")
    }
  }
}

case class ExpReturn(value: Value)(val token: Token) extends Expression {
  override def toString: String = s"return $value"

  // Unref <= ^
  override def checkType(vc: VariableContext, tp: NType): Unit = tp match {
    case NComputation(result) => value.checkType(vc, result)
    case _ => throw TypeException(s"$this does not have type $tp")
  }
}
case class ExpLet(variable: String, value: BoundExpression, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"let $variable = $value; $body"

  // Unref <= let
  override def checkType(vc: VariableContext, tp: NType): Unit =
    body.checkType(vc.add(variable, value.getType(vc).result), tp)
}
case class ExpMatch(head: Head, clauses: MatchPattern)(val token: Token) extends Expression {
  override def toString: String = s"match $head $clauses"

  // Unref <= match
  override def checkType(vc: VariableContext, tp: NType): Unit =
    clauses.checkType(vc, head.getType(vc), tp)
}
case class ExpFunction(variable: String, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"λ$variable . $body"

  // Unref <= λ
  override def checkType(vc: VariableContext, tp: NType): Unit = tp match {
    case NFunction(a, r) => body.checkType(vc.add(variable, a), r)
    case _ => throw TypeException(s"$this does not have type $tp")
  }
}
case class ExpRecursive(variable: String, tp: NType, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"rec $variable : $tp . $body"

  // Unref <= rec
  override def checkType(vc: VariableContext, tp: NType): Unit =
    body.checkType(vc.add(variable, PSuspended(tp)), tp)
  // TODO ^^ does not use the type declaration used for the variable (related to type erasure)
}

// TODO maybe rename? encapsulates all clauses of a match block
sealed trait MatchPattern {
  def checkType(vc: VariableContext, head: PType, tp: NType): Unit
}

object MatchPattern extends Parseable[MatchPattern] {
  override def parse(pc: ParseContext): MatchPattern = {
    val tok = pc.pop(Tk.LBrace)
    val tok2 = pc.pop()
    tok2.tk match {
      case Tk.RBrace => MPVoid()(tok)
      case Tk.LAngle => {
        if pc.peek().tk == Tk.RAngle then {
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          MPUnit(body)(tok)
        } else {
          val left = pc.pop(Tk.Var).text
          pc.pop(Tk.Comma)
          val right = pc.pop(Tk.Var).text
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          MPProd(left, right, body)(tok)
        }
      }
      case Tk.Inl => {
        val left = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val leftBody = Expression.parse(pc)
        pc.pop(Tk.Or)
        pc.pop(Tk.Inr)
        val right = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val rightBody = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPSum(left, leftBody, right, rightBody)(tok)
      }
      case Tk.Inr => {
        val right = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val rightBody = Expression.parse(pc)
        pc.pop(Tk.Or)
        pc.pop(Tk.Inl)
        val left = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val leftBody = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPSum(left, leftBody, right, rightBody)(tok)
      }
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        pc.pop(Tk.DRight)
        val body = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPInto(variable, body)(tok)
      }
      case _ => throw UnexpectedTokenParseException(tok2, "a match pattern")
    }
  }
}

case class MPVoid()(val token: Token) extends MatchPattern {
  override def toString: String = "{}"

  // UnrefMatch0
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PVoid() => ()
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}

case class MPInto(variable: String, body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{into($variable) ⇒ $body}"

  // Unref MatchInto
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    // TODO case ??? ⇒ ???
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class MPUnit(body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{<> ⇒ $body}"

  // UnrefMatch1
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PUnit() => body.checkType(vc, tp)
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class MPProd(left: String, right: String, body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{<$left, $right> ⇒ $body}"

  // UnrefMatch×
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PProd(l, r) => body.checkType(vc.add(left, l).add(right, r), tp)
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class MPSum(left: String, leftBody: Expression, right: String, rightBody: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{inl $left ⇒ $leftBody | inr $right ⇒ $rightBody}"

  // UnrefMatch+
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PSum(l, r) => { leftBody.checkType(vc.add(left, l), tp); rightBody.checkType(vc.add(right, r), tp) }
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}


