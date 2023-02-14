
trait TypeEquality[T] {
  def equivalent(left: T, right: T)(ctx: IndexVariableCtx, alg: AlgorithmicCtx): (SubtypingConstraint, AlgorithmicCtx)

  final def equivalent(left: (T, T), right: (T, T))(ctx: IndexVariableCtx, alg: AlgorithmicCtx): (SubtypingConstraint, AlgorithmicCtx) = {
    val (ll, lr) = left
    val (rl, rr) = right
    val (w1, alg1) = equivalent(ll, rl)(ctx, alg)
    // TODO rr = [alg1]rr
    val (w2, alg2) = equivalent(lr, rr)(ctx, alg1)
    // TODO w1 = [alg2]w1
    (SCConjunction(w1, w2), alg2)
  }
}

sealed trait TypingConstraint {

}


sealed trait SubtypingConstraint {

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
