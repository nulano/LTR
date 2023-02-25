
trait TypeEquality[T] {
  /**
   * Check that left and right are equivalent under context ctx returning output constraint,
   * i.e. Θ ⊢ left ≡ right / W ⊣ Δ (fig. 27/58, 28/60)
   * @param left the left argument
   * @param right the right argument
   * @param ctx the variable context, i.e. Θ
   * @return the output constraint, i.e. W
   */
  def equivalent(left: T, right: T)(ctx: IndexVariableCtx): SubtypingConstraint

  final def equivalent(left: (T, T), right: (T, T))(ctx: IndexVariableCtx): SubtypingConstraint = {
    val (ll, lr) = left
    val (rl, rr) = right
    val w1 = equivalent(ll, rl)(ctx)
    val w2 = equivalent(lr, rr)(ctx)
    SCConjunction(w1, w2)
  }
}

trait TypeSubtype[T] {
  /**
   * Check that left is a subtype of right under context ctx returning output constraint,
   * i.e. Θ ⊢ left <: right / W ⊣ Δ (fig. 30/62)
   * @param left  the left argument
   * @param right the right argument
   * @param ctx   the variable context, i.e. Θ
   * @return the output constraint, i.e. W
   */
  def subtype(left: T, right: T)(ctx: IndexVariableCtx): SubtypingConstraint
}

sealed trait TypingConstraint {
  /**
   * Verify that this constraint holds under context, i.e. `θ; Γ ⊨ this` (fig. 68).
   * @param ctx the logic context, i.e. Θ
   * @param vars the variable context, i.e. Γ
   */
  def check(ctx: LogicCtx, vars: VariableContext): Unit
}

case class TCExpression(expr: Expression, tp: NType) extends TypingConstraint {
  override def toString: String = s"($expr ⇐ $tp)"

  // ◁NegChk
  override def check(ctx: (IndexVariableCtx, PropositionCtx), vars: VariableContext): Unit =
    Expression.checkType(expr, tp.norm)(ctx._1, vars)  // TODO proposition context
}

sealed trait SubtypingConstraint extends TypingConstraint {
  /**
   * Verify that this constraint holds under context, i.e. `θ ⊨ this` (fig. 68).
   * @param ctx  the logic context, i.e. Θ
   */
  def check(ctx: LogicCtx): Unit
  
  final override def check(ctx: (IndexVariableCtx, PropositionCtx), vars: VariableContext): Unit = check(ctx)
}

case class SCConjunction(constraints: List[SubtypingConstraint]) extends SubtypingConstraint {
  override def toString: String = constraints.mkString("(", " ∧ ", ")")

  // ⊨W∧
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit =
    constraints.foreach(_.check(ctx))
}
object SCConjunction {
  def apply(left: SubtypingConstraint, right: SubtypingConstraint): SCConjunction = {
    (left, right) match {
      case (SCConjunction(l), SCConjunction(r)) => SCConjunction(l ++ r)
      case (SCConjunction(l), _) => SCConjunction(l :+ right)
      case (_, SCConjunction(r)) => SCConjunction(left +: r)
      case (_, _) => SCConjunction(List(left, right))
    }
  }
}
case class SCProposition(proposition: Proposition) extends SubtypingConstraint {
  override def toString: String = proposition.toString

  // ⊨WPrp
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit = {
    if proposition != IPTrue then {
      // TODO call SMT solver
      println(s"!! SMT solver not implemented, assuming ${ctx._2.mkString(", ")} ⊨ ${proposition.norm}")
    }
  }
}
val SCTrue: SCProposition = SCProposition(IPTrue)
case class SCEquivalent(left: Proposition, right: Proposition) extends SubtypingConstraint {
  override def toString: String = s"$left ≡ $right"

  // ⊨WPrp≡
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit = {
    // TODO call SMT solver
    println(s"!! SMT solver not implemente, assuming ${ctx._2.mkString(", ")} ⊨ ${left.norm} ≡ ${right.norm}")
  }
}
case class SCPrecondition(proposition: Proposition, rest: SubtypingConstraint) extends SubtypingConstraint {
  override def toString: String = s"$proposition ⊃ $rest"

  // ⊨W⊃
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit = {
    rest.check((ctx._1, ctx._2 :+ proposition))
  }
}
case class SCForAll(variable: IndexVariable, rest: SubtypingConstraint) extends SubtypingConstraint {
  override def toString: String = s"∀${variable.name} : ${variable.sort} . $rest"

  // ⊨W∀
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit = {
    rest.check((ctx._1 + variable, ctx._2))
  }
}
case class SCPSubtype(left: PType, right: PType) extends SubtypingConstraint {
  override def toString: String = s"$left <:⁺ $right"

  // ⊨W<:⁺
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit =
    PType.subtype(left, right)(ctx._1).check(ctx)
}
case class SCNSubtype(left: NType, right: NType) extends SubtypingConstraint {
  override def toString: String = s"$left <:⁻ $right"

  // ⊨W<:⁻
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit =
    NType.subtype(left, right)(ctx._1).check(ctx)
}
case class SCPEquivalent(left: PType, right: PType) extends SubtypingConstraint {
  override def toString: String = s"$left ≡⁺ $right"

  // ⊨W<:⁺
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit =
    PType.equivalent(left, right)(ctx._1).check(ctx)
}
case class SCNEquivalent(left: NType, right: NType) extends SubtypingConstraint {
  override def toString: String = s"$left ≡⁻ $right"

  // ⊨W<:⁻
  override def check(ctx: (IndexVariableCtx, PropositionCtx)): Unit =
    NType.equivalent(left, right)(ctx._1).check(ctx)
}
