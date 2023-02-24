
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

}

case class TCExpression(expr: Expression, tp: NType) extends TypingConstraint {
  override def toString: String = s"($expr ⇐ $tp)"
}

sealed trait SubtypingConstraint extends TypingConstraint {

}

case class SCConjunction(constraints: List[SubtypingConstraint]) extends SubtypingConstraint {
  override def toString: String = constraints.mkString("(", " ∧ ", ")")
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
}
val SCTrue: SCProposition = SCProposition(IPTrue)
case class SCEquivalent(left: Proposition, right: Proposition) extends SubtypingConstraint {
  override def toString: String = s"$left ≡ $right"
}
case class SCPrecondition(proposition: Proposition, rest: SubtypingConstraint) extends SubtypingConstraint {
  override def toString: String = s"$proposition ⊃ $rest"
}
case class SCForAll(variable: IndexVariable, rest: SubtypingConstraint) extends SubtypingConstraint {
  override def toString: String = s"∀${variable.name} : ${variable.sort} . $rest"
}
case class SCPSubtype(left: PType, right: PType) extends SubtypingConstraint {
  override def toString: String = s"$left <:⁺ $right"
}
case class SCNSubtype(left: NType, right: NType) extends SubtypingConstraint {
  override def toString: String = s"$left <:⁻ $right"
}
case class SCPEquivalent(left: PType, right: PType) extends SubtypingConstraint {
  override def toString: String = s"$left ≡⁺ $right"
}
case class SCNEquivalent(left: NType, right: NType) extends SubtypingConstraint {
  override def toString: String = s"$left ≡⁻ $right"
}
