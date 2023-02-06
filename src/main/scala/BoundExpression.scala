
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
      case _ => throw UnexpectedTokenParseException(tok, "a head")
    }
  }
}

case class HeadVariable(variable: String)(val token: Token) extends Head {
  override def toString: String = variable

  // Unref ⇒ Var
  override def getType(vc: VariableContext): PType = vc.find(variable).get
}
case class HeadValue(value: Value, tp: PType)(val token: Token) extends Head {
  override def toString: String = s"[$value : $tp]"

  // Unref ⇒ ValAnnot
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
      val head = Head.parse(pc)  // TODO custom exception?
      pc.pop(Tk.LParen)
      val spine = new collection.immutable.VectorBuilder[Value]()
      if pc.peek().tk == Tk.RParen then {
        pc.pop(Tk.RParen)
      } else {
        spine += Value.parse(pc)
        while pc.pop(Tk.Comma, Tk.RParen).tk == Tk.Comma do
          spine += Value.parse(pc)
      }
      BEApplication(head, spine.result())(tok)
    }
  }
}

case class BEApplication(head: Head, spine: Vector[Value])(val token: Token) extends BoundExpression {
  override def toString: String = s"$head(${spine.mkString(",")})"

  // Unref ⇒ App
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

  // Unref ⇒ ExpAnnot
  override def getType(vc: VariableContext): NComputation = { exp.checkType(vc, resultType); resultType }
}