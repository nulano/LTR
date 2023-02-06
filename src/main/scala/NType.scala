sealed trait NType extends WellFormed, SubstitutableIndex[NType]
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

  // AlgTp→
  override def wellFormed(ctx: Set[IndexVariable]): Set[IndexVariable] =
    arg.wellFormed(ctx) | body.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): NFunction =
    NFunction((replacement / target)(arg), (replacement / target)(body))
}
case class NComputation(result: PType) extends NTypeBase[NComputation] {
  override def toString: String = s"↑$result"

  // AlgTp↑
  override def wellFormed(ctx: Set[IndexVariable]): Set[IndexVariable] =
  { result.wellFormed(ctx); Set.empty }

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

  // AlgTp∀
  override def wellFormed(ctx: Set[IndexVariable]): Set[IndexVariable] = {
    val body = tp.wellFormed(ctx + variable)
    if !body.contains(variable) then
      throw TypeException(s"cannot determine value of universally quantified index: $this")
    body - variable
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): NForAll =
    NForAll(variable, (replacement / target)(tp))
}
case class NPrecondition(proposition: Proposition, tp: NType) extends NTypeBase[NPrecondition] {
  override def toString: String = s"[$proposition] ⊃ $tp"

  // AlgTp⊃
  override def wellFormed(ctx: Set[IndexVariable]): Set[IndexVariable] = {
    proposition.sort(ctx); tp.wellFormed(ctx)
  }
  
  override def substituteIndex(replacement: Index, target: IndexVariable): NPrecondition =
    NPrecondition((replacement / target)(proposition), (replacement / target)(tp))
}
