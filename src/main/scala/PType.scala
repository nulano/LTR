sealed trait PType

object PType extends Parseable[PType] {
  def parse(pc: ParseContext): PType = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var if tok.text == "1" => PUnit()
      case Tk.Var if tok.text == "0" => PVoid()
      case Tk.LParen => {
        val left = PType.parse(pc)
        val op = pc.pop(Tk.Times, Tk.Plus, Tk.And)
        if op.tk == Tk.And then {
          val right = pc.pop()  // TODO
          pc.pop(Tk.RParen)
          PProperty(left, right.text)
        } else {
          val right = PType.parse(pc)
          pc.pop(Tk.RParen)
          if op.tk == Tk.Times then
            PProd(left, right)
          else
            PSum(left, right)
        }
      }
      case Tk.Down => PSuspended(NType.parse(pc))
      // TODO case Tk.LBrace => PInductive(...)
      case Tk.Mu => {
        val fun = FunctorSum.parse(pc)
        pc.pop(Tk.Superset)
        val alg = pc.pop(Tk.Var).text // TODO
        pc.pop(Tk.DRight)
        val idx = pc.pop(Tk.Var).text // TODO
        PInductive(fun, alg, idx)
      }
      case Tk.Exists => {
        val idx = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val sort = Sort.parse(pc)
        pc.pop(Tk.Dot)
        val tp = PType.parse(pc)
        PExists(idx, sort, tp)
      }
      case _ => throw UnexpectedTokenParseException(tok, "a positive type")
    }
  }
}

case class PUnit() extends PType {
  override def toString: String = "1"
}
case class PProd(left: PType, right: PType) extends PType {
  override def toString: String = s"($left × $right)"
}
case class PVoid() extends PType {
  override def toString: String = "0"
}
case class PSum(left: PType, right: PType) extends PType {
  override def toString: String = s"($left + $right)"
}
case class PSuspended(tp: NType) extends PType {
  override def toString: String = s"↓$tp"
}
// TODO algebra, index types
case class PInductive(functor: FunctorSum, algebra: String, idx: String) extends PType {
  // TODO actual string is s"{v : μ$functor | (fold_$functor $algebra) v =_τ $idx}"
  override def toString: String = s"μ$functor ⊃ $algebra ⇒ $idx"
  
  def unroll: PType = functor.unroll(this)
}
case class PExists(idx: String, sort: Sort, tp: PType) extends PType {
  override def toString: String = s"∃$idx : $sort . $tp"
}
// TODO proposition type
case class PProperty(tp: PType, proposition: String) extends PType {
  override def toString: String = s"($tp ∧ $proposition)"
}
