sealed trait PType extends WellFormed, SubstitutableIndex[PType]
sealed trait PTypeBase[T <: PTypeBase[T]] extends PType, SubstitutableIndex[T]

object PType extends Parseable[PType], TypeEquality[PType] {
  override def parse(pc: ParseContext): PType = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Number if tok.text == "1" => PUnit
      case Tk.Number if tok.text == "0" => PVoid
      case Tk.LParen =>
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
      case Tk.Down => PSuspended(NType.parse(pc))
      // TODO case Tk.LBrace => PInductive(...)
      case Tk.Mu =>
        val fun = FunctorSum.parse(pc)
        pc.pop(Tk.Superset)
        val alg = Algebra.parse(pc)
        pc.pop(Tk.DRight)
        val idx = Index.parse(pc)
        PInductive(fun, alg, idx)
      case Tk.Exists =>
        val variable = IVBound.parse(pc)
        pc.pop(Tk.Dot)
        val tp = PType.parse(pc + variable)
        PExists(variable, tp)
      case Tk.Var => pc.getTypeVar(tok)
      case _ => throw UnexpectedTokenParseException(tok, "a positive type")
    }
  }

  override def equivalent(left: PType, right: PType)(ctx: IndexVariableCtx): SubtypingConstraint = {
    (left, right) match
      // Tp≡⁺/⊣1
      case (PUnit, PUnit) => SCTrue
      // Tp≡⁺/⊣0
      case (PVoid, PVoid) => SCTrue
      // Tp≡⁺/⊣×
      case (PProd(ll, lr), PProd(rl, rr)) => PType.equivalent((ll, lr), (rl, rr))(ctx)
      // Tp≡⁺/⊣+
      case (PSum(ll, lr), PSum(rl, rr)) => PType.equivalent((ll, lr), (rl, rr))(ctx)
      // Tp≡⁺/⊣∧
      case (PProperty(lt, lp), PProperty(rt, rp)) =>
        val w1 = PType.equivalent(lt, rt)(ctx)
        (lp, rp) match {
          // PropEquivInst
          case (IPEqual(la, _), IPEqual(IVariable(rav: IVAlgorithmic), _)) if rav.solution.isEmpty =>
            val ls = la.sort(ctx)
            if ls == rav.sort then
              rav.solution = Some(la)
            // TODO else ???
          case _ => ()
        }
        SCConjunction(w1, SCEquivalent(lp, rp))
      // Tp≡⁺/⊣∃
      case (PExists(lv, lt), PExists(rv, rt)) if lv.sort == rv.sort =>
        val temp = IVariable(new IVBound(lv.name, lv.sort))
        val w = PType.equivalent((temp / lv)(lt), (temp / rv)(rt))(ctx + temp.variable)
        SCForAll(temp.variable, w)
      // Tp≡⁺/⊣μ
      case (PInductive(lf, la, li), PInductive(rf, ra, ri)) if la == ra =>
        val w1 = Functor.equivalent(lf, rf)(ctx)
        ri match
          case IVariable(rv: IVAlgorithmic) if rv.solution.isEmpty =>
            // TODO only if li ground
            rv.solution = Option(li)
          case _ => ()
            // TODO if solved by functor equivalence above, skip this
            // TODO check ∀â ∈ dom(alg) . [alg]ri ≠ â
        SCConjunction(w1, SCProposition(IPEqual(li, ri)))
      // Tp≡⁺/⊣↓
      case (PSuspended(l), PSuspended(r)) => SCNEquivalent(l, r)
      case _ => throw TypeException(s"positive types are not equivalent: $left ≢ $right")
  }
}

object PUnit extends PTypeBase[PUnit.type] {
  override def toString: String = "1"

  // AlgTp1
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = Set.empty

  override def substituteIndex(replacement: Index, target: IndexVariable): PUnit.type = this
}
case class PProd(left: PType, right: PType) extends PTypeBase[PProd] {
  override def toString: String = s"($left × $right)"

  // AlgTp×
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) | right.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): PProd =
    PProd((replacement / target)(left), (replacement / target)(right))
}
object PVoid extends PTypeBase[PVoid.type] {
  override def toString: String = "0"

  // AlgTp0
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = Set.empty

  override def substituteIndex(replacement: Index, target: IndexVariable): PVoid.type = this
}
case class PSum(left: PType, right: PType) extends PTypeBase[PSum] {
  override def toString: String = s"($left + $right)"

  // AlgTp+
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) & right.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): PSum =
    PSum((replacement / target)(left), (replacement / target)(right))
}
case class PSuspended(tp: NType) extends PTypeBase[PSuspended] {
  override def toString: String = s"↓$tp"

  // AlgTp↓
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
  { tp.wellFormed(ctx); Set.empty }

  override def substituteIndex(replacement: Index, target: IndexVariable): PSuspended =
    PSuspended((replacement / target)(tp))
}
case class PInductive(functor: FunctorSum, algebra: Algebra, index: Index) extends PTypeBase[PInductive] {
  // TODO actual string is s"{v : μ$functor | (fold_$functor $algebra) v =_τ $idx}"
  override def toString: String = s"μ$functor ⊃ $algebra ⇒ $index"

  def unroll: PType = functor.unroll(this)

  // AlgTpμ{...}
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = {
    val functorDetermined = functor.wellFormed(ctx)
    val sort = index.sort(ctx)
    Algebra.wellFormed(Set.empty, ctx, algebra, functor, sort)
    index match {
      case variable: IVariable => functorDetermined + variable.variable
      case _ => functorDetermined
    }
  }

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
        // TODO different var class?
        val temp = IVariable(new IVBound(variable.name, variable.sort))
        (temp / this.variable)(this.tp) == (temp / that.variable)(that.tp)
      case _ => false
    }

  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = {
    val body = tp.wellFormed(ctx + variable)
    if !body.contains(variable) then
      throw TypeException(s"cannot determine value of existentially quantified index: $this")
    body - variable
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): PExists =
    PExists(variable, tp)
}
case class PProperty(tp: PType, proposition: Proposition) extends PTypeBase[PProperty] {
  override def toString: String = s"($tp ∧ [$proposition])"

  // AlgTp∧
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
  { proposition.sort(ctx); tp.wellFormed(ctx) }

  override def substituteIndex(replacement: Index, target: IndexVariable): PProperty =
    PProperty((replacement / target)(tp), (replacement / target)(proposition))
}
