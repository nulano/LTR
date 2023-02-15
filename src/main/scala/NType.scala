sealed trait NType extends WellFormed, SubstitutableIndex[NType]
sealed trait NTypeBase[T <: NTypeBase[T]] extends NType, SubstitutableIndex[T]

object NType extends Parseable[NType], TypeEquality[NType] {
  override def parse(pc: ParseContext): NType = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.LParen =>
        val arg = PType.parse(pc)
        pc.pop(Tk.Right)
        val body = NType.parse(pc)
        pc.pop(Tk.RParen)
        NFunction(arg, body)
      case Tk.Up => NComputation(PType.parse(pc))
      case Tk.ForAll =>
        val variable = IVBound.parse(pc)
        pc.pop(Tk.Dot)
        val tp = NType.parse(pc + variable)
        NForAll(variable, tp)
      case Tk.LSquare =>
        val proposition = Proposition.parse(pc)
        pc.pop(Tk.RSquare)
        pc.pop(Tk.Superset)
        val tp = NType.parse(pc)
        NPrecondition(proposition, tp)
      case _ => throw UnexpectedTokenParseException(tok, "a negative type")
    }
  }

  override def equivalent(left: NType, right: NType)
                         (ctx: IndexVariableCtx, alg: AlgorithmicCtx): (SubtypingConstraint, AlgorithmicCtx) = {
    (left, right) match {
      // Tp≡⁻/⊣↑
      case (NComputation(l), NComputation(r)) => (SCPEquivalent(l, r), alg)
      // Tp≡⁻/⊣⊃
      case (NPrecondition(lp, lt), NPrecondition(rp, rt)) =>
        val (w1, alg1) = NType.equivalent(lt, rt)(ctx, alg)
        // TODO lp = [alg1]lp
        val w2 = SCEquivalent(lp, rp)
        (SCConjunction(w1, w2), alg1)
      // Tp≡⁻/⊣∀
      case (NForAll(lv, lt), NForAll(rv, rt)) =>
        val temp = IVariable(new IVBound(lv.name, lv.sort))
        val (w, alg2) = NType.equivalent((temp / lv)(lt), (temp / rv)(rt))(ctx + temp.variable, alg)
        (SCForAll(temp.variable, w), alg2)
      // Tp≡⁻/⊣→
      case (NFunction(la, lb), NFunction(ra, rb)) =>
        val (w1, alg1) = PType.equivalent(la, ra)(ctx, alg)
        // TODO lb = [alg1]lb
        val (w2, alg2) = NType.equivalent(lb, rb)(ctx, alg1)
        // TODO w1 = [alg1]w1
        (SCConjunction(w1, w2), alg2)
      case _ => throw TypeException(s"negative types are not equivalent: $left ≢ $right")
    }
  }
}

case class NFunction(arg: PType, body: NType) extends NTypeBase[NFunction] {
  override def toString: String = s"($arg → $body)"

  // AlgTp→
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    arg.wellFormed(ctx) | body.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): NFunction =
    NFunction((replacement / target)(arg), (replacement / target)(body))
}
case class NComputation(result: PType) extends NTypeBase[NComputation] {
  override def toString: String = s"↑$result"

  // AlgTp↑
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
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
        val temp = IVariable(new IVBound(variable.name, variable.sort))
        (temp / this.variable)(this.tp) == (temp / that.variable)(that.tp)
      case _ => false
    }

  // AlgTp∀
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = {
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
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = {
    proposition.sort(ctx); tp.wellFormed(ctx)
  }
  
  override def substituteIndex(replacement: Index, target: IndexVariable): NPrecondition =
    NPrecondition((replacement / target)(proposition), (replacement / target)(tp))
}
