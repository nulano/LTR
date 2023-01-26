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
        val idx = pc.pop(Tk.Var)
        pc.pop(Tk.Colon)
        val sort = pc.pop(Tk.Var) // TODO
        pc.pop(Tk.Dot)
        val tp = NType.parse(pc)
        NForAll(idx.text, sort.text, tp)
      }
      // TODO case ??? => NPrecondition
      case _ => throw ParseException(s"not an n-type: ${tok.text}")
    }
  }
}

case class NFunction(arg: PType, body: NType) extends NType {
  override def toString: String = s"($arg → $body)"
}
case class NComputation(result: PType) extends NType {
  override def toString: String = s"↑$result"
}
// TODO sort class
case class NForAll(idx: String, sort: String, tp: NType) extends NType {
  override def toString: String = s"∀$idx : $sort . $tp"
}
// TODO proposition class
case class NPrecondition(proposition: String, tp: NType) extends NType {
  override def toString: String = s"$proposition ⊃ $tp"
}
