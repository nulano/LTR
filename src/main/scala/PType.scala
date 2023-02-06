sealed trait PType extends SubstitutableIndex[PType]
sealed trait PTypeBase[T <: PTypeBase[T]] extends PType, SubstitutableIndex[T]

object PType extends Parseable[PType] {
  def parse(pc: ParseContext): PType = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Number if tok.text == "1" => PUnit()
      case Tk.Number if tok.text == "0" => PVoid()
      case Tk.LParen => {
        val left = PType.parse(pc)
        val op = pc.pop(Tk.Times, Tk.Plus, Tk.And)
        if op.tk == Tk.And then {
          pc.pop(Tk.LSquare)
          val right = Proposition.parse(pc)
          pc.pop(Tk.RSquare)
          pc.pop(Tk.RParen)
          PProperty(left, right)
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
        val alg = Algebra.parse(pc)
        pc.pop(Tk.DRight)
        val idx = Index.parse(pc)
        PInductive(fun, alg, idx)
      }
      case Tk.Exists => {
        val variable = IndexVariable.parse(pc)
        pc.pop(Tk.Dot)
        val tp = PType.parse(pc + variable)
        PExists(variable, tp)
      }
      case Tk.Var => pc.getTypeVar(tok)
      case _ => throw UnexpectedTokenParseException(tok, "a positive type")
    }
  }
}

case class PUnit() extends PTypeBase[PUnit] {
  override def toString: String = "1"

  override def substituteIndex(replacement: Index, target: IndexVariable): PUnit = this
}
case class PProd(left: PType, right: PType) extends PTypeBase[PProd] {
  override def toString: String = s"($left × $right)"

  override def substituteIndex(replacement: Index, target: IndexVariable): PProd =
    PProd((replacement / target)(left), (replacement / target)(right))
}
case class PVoid() extends PTypeBase[PVoid] {
  override def toString: String = "0"

  override def substituteIndex(replacement: Index, target: IndexVariable): PVoid = this
}
case class PSum(left: PType, right: PType) extends PTypeBase[PSum] {
  override def toString: String = s"($left + $right)"

  override def substituteIndex(replacement: Index, target: IndexVariable): PSum =
    PSum((replacement / target)(left), (replacement / target)(right))
}
case class PSuspended(tp: NType) extends PTypeBase[PSuspended] {
  override def toString: String = s"↓$tp"

  override def substituteIndex(replacement: Index, target: IndexVariable): PSuspended =
    PSuspended((replacement / target)(tp))
}
case class PInductive(functor: FunctorSum, algebra: Algebra, index: Index) extends PTypeBase[PInductive] {
  // TODO actual string is s"{v : μ$functor | (fold_$functor $algebra) v =_τ $idx}"
  override def toString: String = s"μ$functor ⊃ $algebra ⇒ $index"

  def unroll: PType = functor.unroll(this)

  // TODO consider algebra?
  override def substituteIndex(replacement: Index, target: IndexVariable): PInductive =
    PInductive(functor, algebra, (replacement / target)(index))
}
case class PExists(variable: IndexVariable, tp: PType) extends PTypeBase[PExists] {
  override def toString: String = s"∃${variable.name} : ${variable.sort} . $tp"

  // hashCode of IVariable be 0 to allow for simple α-equivalence of ∀ and ∃ types
  override def hashCode(): Int = tp.hashCode()

  override def equals(other: Any): Boolean =
    other match {
      case that: PExists =>
        val temp = IVariable(new IndexVariable(variable.name, variable.sort))
        (temp / this.variable)(this.tp) == (temp / that.variable)(that.tp)
      case _ => false
    }

  override def substituteIndex(replacement: Index, target: IndexVariable): PExists =
    PExists(variable, tp)
}
case class PProperty(tp: PType, proposition: Proposition) extends PTypeBase[PProperty] {
  override def toString: String = s"($tp ∧ [$proposition])"

  override def substituteIndex(replacement: Index, target: IndexVariable): PProperty =
    PProperty((replacement / target)(tp), (replacement / target)(proposition))
}
