sealed trait NType

object NType extends Parseable[NType] {
  def parse(pc: ParseContext): NType = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.LParen => {
        val arg = PType.parse(pc)
        pc.pop(Tk.Right)
        val body = NType.parse(pc)
        pc.pop(Tk.RParen)
        NFunction(arg, body)
      }
      case Tk.Up => NComputation(PType.parse(pc))
      case Tk.ForAll => {
        val idx = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val sort = Sort.parse(pc)
        pc.pop(Tk.Dot)
        val tp = NType.parse(pc)
        NForAll(idx, sort, tp)
      }
      // TODO case ??? => NPrecondition
      case _ => throw UnexpectedTokenParseException(tok, "a negative type")
    }
  }
}

case class NFunction(arg: PType, body: NType) extends NType {
  override def toString: String = s"($arg → $body)"
}
case class NComputation(result: PType) extends NType {
  override def toString: String = s"↑$result"
}
case class NForAll(idx: String, sort: Sort, tp: NType) extends NType {
  override def toString: String = s"∀$idx : $sort . $tp"
}
// TODO proposition class
case class NPrecondition(proposition: String, tp: NType) extends NType {
  override def toString: String = s"$proposition ⊃ $tp"
}
