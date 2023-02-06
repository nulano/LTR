sealed trait NType extends SubstitutableIndex[NType]
sealed trait NTypeBase[T <: NTypeBase[T]] extends NType, SubstitutableIndex[T]

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
        val variable = IVSimple.parse(pc)
        pc.pop(Tk.Dot)
        val tp = NType.parse(pc + variable)
        NForAll(variable, tp)
      }
      case Tk.LSquare =>
        val proposition = Proposition.parse(pc)
        pc.pop(Tk.RSquare)
        pc.pop(Tk.Superset)
        val tp = NType.parse(pc)
        NPrecondition(proposition, tp)
      case _ => throw UnexpectedTokenParseException(tok, "a negative type")
    }
  }
}

case class NFunction(arg: PType, body: NType) extends NTypeBase[NFunction] {
  override def toString: String = s"($arg → $body)"

  override def substituteIndex(replacement: Index, target: IndexVariable): NFunction =
    NFunction((replacement / target)(arg), (replacement / target)(body))
}
case class NComputation(result: PType) extends NTypeBase[NComputation] {
  override def toString: String = s"↑$result"

  override def substituteIndex(replacement: Index, target: IndexVariable): NComputation =
    NComputation((replacement / target)(result))
}
case class NForAll(variable: IndexVariable, tp: NType) extends NTypeBase[NForAll] {
  override def toString: String = s"∀${variable.name} : ${variable.sort} . $tp"

  // hashCode of IVariable be 0 to allow for simple α-equivalence of ∀ and ∃ types
  override def hashCode(): Int = tp.hashCode()

  override def equals(other: Any): Boolean =
    other match {
      case that: NForAll =>
        // TODO different var class?
        val temp = IVariable(new IVSimple(variable.name, variable.sort))
        (temp / this.variable)(this.tp) == (temp / that.variable)(that.tp)
      case _ => false
    }

  override def substituteIndex(replacement: Index, target: IndexVariable): NForAll =
    NForAll(variable, (replacement / target)(tp))
}
case class NPrecondition(proposition: Proposition, tp: NType) extends NTypeBase[NPrecondition] {
  override def toString: String = s"[$proposition] ⊃ $tp"

  override def substituteIndex(replacement: Index, target: IndexVariable): NPrecondition =
    NPrecondition((replacement / target)(proposition), (replacement / target)(tp))
}
