
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
        val clauses = Pattern.parse(pc)
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
      case _ => throw ParseException("not an expression: " + tok)
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
case class ExpMatch(head: Head, clauses: Pattern)(val token: Token) extends Expression {
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

sealed trait Head {
  def getType(vc: VariableContext): PType
}

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

  // Unref => Var
  override def getType(vc: VariableContext): PType = vc.find(variable).get
}
case class HeadValue(value: Value, tp: PType)(val token: Token) extends Head {
  override def toString: String = s"[$value : $tp]"

  // Unref => ValAnnot
  override def getType(vc: VariableContext): PType = { value.checkType(vc, tp); tp }
}

sealed trait BoundExpression {
  def getType(vc: VariableContext): NComputation
}

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
        spine += Value.parse(pc)
        pc.pop(Tk.Comma)
      }
      pc.pop(Tk.RParen)
      BEApplication(head, spine.result())(tok)
    }
  }
}

case class BEApplication(head: Head, spine: Vector[Value])(val token: Token) extends BoundExpression {
  override def toString: String = s"$head(${spine.mkString(",")})"

  // Unref => App
  override def getType(vc: VariableContext): NComputation = {
    val headType = head.getType(vc)
    headType match {
      case PSuspended(tp) => {
        // need to check: Γ; [$tp] ⊢ $spine ≫ ↑P
        // UnrefSpineApp
        val res = spine.foldLeft(tp)((t: NType, v: Value) => t match {
          case NFunction(arg, body) => { v.checkType(vc, arg); body }
          case _ => throw TypeException(s"too many arguments")
        })
        // UnrefSpineNil
        res match {
          case comp: NComputation => comp
          case _ => throw TypeException(s"too few arguments")
        }
      }
      case _ => throw TypeException(s"type '$headType' is not a suspended computation")
    }
  }
}
case class BEExpression(exp: Expression, tp: PType)(val token: Token) extends BoundExpression {
  val resultType: NComputation = NComputation(tp)

  override def toString: String = s"($exp : $resultType)"

  // Unref => ExpAnnot
  override def getType(vc: VariableContext): NComputation = { exp.checkType(vc, resultType); resultType }
}

// TODO maybe rename? encapsulates all clauses of a match block
sealed trait Pattern {
  def checkType(vc: VariableContext, head: PType, tp: NType): Unit
}

object Pattern extends Parseable[Pattern] {
  override def parse(pc: ParseContext): Pattern = {
    val tok = pc.pop(Tk.LBrace)
    pc.pop().tk match {
      case Tk.RBrace => PatVoid()(tok)
      case Tk.LAngle => {
        if pc.peek().tk == Tk.RAngle then {
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          PatUnit(body)(tok)
        } else {
          val left = pc.pop(Tk.Var).text
          pc.pop(Tk.Comma)
          val right = pc.pop(Tk.Var).text
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          PatProd(left, right, body)(tok)
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
        PatSum(left, leftBody, right, rightBody)(tok)
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
        PatSum(left, leftBody, right, rightBody)(tok)
      }
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        pc.pop(Tk.DRight)
        val body = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        PatInto(variable, body)(tok)
      }
      case t => throw ParseException(s"not a pattern: ${t.text}")
    }
  }
}

case class PatVoid()(val token: Token) extends Pattern {
  override def toString: String = "{}"

  // UnrefMatch0
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PVoid() => ()
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}

case class PatInto(variable: String, body: Expression)(val token: Token) extends Pattern {
  override def toString: String = s"{into($variable) ⇒ $body}"

  // Unref MatchInto
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    // TODO case ??? => ???
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class PatUnit(body: Expression)(val token: Token) extends Pattern {
  override def toString: String = s"{<> ⇒ $body}"

  // UnrefMatch1
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PUnit() => body.checkType(vc, tp)
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class PatProd(left: String, right: String, body: Expression)(val token: Token) extends Pattern {
  override def toString: String = s"{<$left, $right> ⇒ $body}"

  // UnrefMatch×
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PProd(l, r) => body.checkType(vc.add(left, l).add(right, r), tp)
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}
case class PatSum(left: String, leftBody: Expression, right: String, rightBody: Expression)(val token: Token) extends Pattern {
  override def toString: String = s"{inl $left ⇒ $leftBody | inr $right ⇒ $rightBody}"

  // UnrefMatch+
  override def checkType(vc: VariableContext, head: PType, tp: NType): Unit = head match {
    case PSum(l, r) => { leftBody.checkType(vc.add(left, l), tp); rightBody.checkType(vc.add(right, r), tp) }
    case _ => throw TypeException(s"{$this} pattern does not match $head")
  }
}


