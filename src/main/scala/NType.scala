sealed trait NType extends Extracts[NType], WellFormed, SubstitutableIndex[NType] {
  override def extract: (NType, LogicCtx) = (this, LogicCtx(Set.empty, List.empty))
}
sealed trait NTypeBase[T <: NTypeBase[T]] extends NType, SubstitutableIndex[T]

object NType extends Parseable[NType], TypeEquality[NType], TypeSubtype[NType] {
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

  override def equivalent(left: NType, right: NType)(ctx: IndexVariableCtx): SubtypingConstraint = {
    (left, right) match {
      // Tp≡⁻/⊣↑
      case (NComputation(l), NComputation(r)) => SCPEquivalent(l, r)
      // Tp≡⁻/⊣⊃
      case (NPrecondition(lp, lt), NPrecondition(rp, rt)) =>
        val w1 = NType.equivalent(lt, rt)(ctx)
        val w2 = SCEquivalent(lp, rp)
        SCConjunction(w1, w2)
      // Tp≡⁻/⊣∀
      case (NForAll(lv, lt), NForAll(rv, rt)) if lv.sort == rv.sort =>
        val temp = IVariable(new IVBound(lv.name, lv.sort))
        val w = NType.equivalent((temp / lv)(lt), (temp / rv)(rt))(ctx + temp.variable)
        SCForAll(temp.variable, w)
      // Tp≡⁻/⊣→
      case (NFunction(la, lb), NFunction(ra, rb)) =>
        val w1 = PType.equivalent(la, ra)(ctx)
        val w2 = NType.equivalent(lb, rb)(ctx)
        SCConjunction(w1, w2)
      case _ => throw TypeException(s"negative types are not equivalent: $left ≢ $right")
    }
  }

  override def subtype(left: NType, right: NType)(ctx: IndexVariableCtx): SubtypingConstraint = {
    (left, right) match {
      // <:⁻/⊣↑
      case (NComputation(l), NComputation(r)) =>
        val (le, lc) = l.extract
        val w1 = lc.propositions.foldRight(SCPSubtype(le, r))(SCPrecondition.apply)
        // TODO this is unclear in the type rules - should SCForAll be used?
        lc.idxVars.foldRight(w1)(SCForAll.apply)
      // <:⁻/⊣⊃L
      case (NPrecondition(lp, lt), _) =>
        val w1 = NType.subtype(lt, right)(ctx)
        val w2 = SCProposition(lp)
        SCConjunction(w1, w2)
      // <:⁻/⊣∀L
      case (NForAll(lv, lt), _) =>
        val temp = new IVAlgorithmic(lv)
        val w = NType.subtype((IVariable(temp) / lv)(lt), right)(ctx + temp)
        if temp.solution.isEmpty then
          throw TypeException(s"failed to determine algorithmic variable $temp")
        else w
      // <:⁻/⊣→
      case (NFunction(la, lb), NFunction(ra, rb)) =>
        val w1 = PType.subtype(ra, la)(ctx)
        val w2 = NType.subtype(lb, rb)(ctx)
        SCConjunction(w1, w2)
      case _ => throw TypeException(s"negative types are not subtypes: $left </: $right")
    }
  }
}

case class NFunction(arg: PType, body: NType) extends NTypeBase[NFunction] {
  override def toString: String = s"($arg → $body)"

  // ⇝⁻→
  override def extract: (NType, LogicCtx) = {
    val (le, lc) = arg.extract
    val (re, rc) = body.extract
    (NFunction(le, re), lc ++ rc)
  }

  // AlgTp→
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    arg.wellFormed(ctx) | body.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): NFunction =
    NFunction((replacement / target)(arg), (replacement / target)(body))

  override def norm: NFunction = NFunction(arg.norm, body.norm)
}
case class NComputation(result: PType) extends NTypeBase[NComputation] {
  override def toString: String = s"↑$result"

  // AlgTp↑
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
  { result.wellFormed(ctx); Set.empty }

  override def substituteIndex(replacement: Index, target: IndexVariable): NComputation =
    NComputation((replacement / target)(result))

  override def norm: NComputation = NComputation(result.norm)
}
case class NForAll(variable: IndexVariable, tp: NType) extends NTypeBase[NForAll] {
  override def toString: String = s"∀$variable . $tp"

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

  // ⇝⁻∀
  override def extract: (NType, LogicCtx) = {
    val temp = new IVBound(variable.name, variable.sort)
    val (tpe, ctx) = (IVariable(temp) / variable)(tp).extract
    (tpe, ctx + temp)
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

  override def norm: NForAll = NForAll(variable, tp.norm)
}
case class NPrecondition(proposition: Proposition, tp: NType) extends NTypeBase[NPrecondition] {
  override def toString: String = s"[$proposition] ⊃ $tp"

  // ⇝⁻⊃
  override def extract: (NType, LogicCtx) = {
    val (tpe, ctx) = tp.extract
    (tpe, ctx + proposition)
  }

  // AlgTp⊃
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = {
    proposition.sort(ctx); tp.wellFormed(ctx)
  }
  
  override def substituteIndex(replacement: Index, target: IndexVariable): NPrecondition =
    NPrecondition((replacement / target)(proposition), (replacement / target)(tp))

  override def norm: NPrecondition = NPrecondition(proposition.norm, tp.norm)
}
