
sealed trait Functor extends WellFormed
sealed trait FunctorSum extends Functor {
  def unroll(id: PInductive): PType
}
sealed trait FunctorProduct extends FunctorSum
sealed trait FunctorBase extends Functor

object Functor extends Parseable[Functor], TypeEquality[Functor] {
  override def parse(pc: ParseContext): Functor = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.LParen =>
        Functor.parse(pc) match {
          case sum: FunctorSum =>
            pc.pop(Tk.CPlus)
            val right = FunctorSum.parse(pc)
            pc.pop(Tk.RParen)
            FSum(sum, right)
          case base: FunctorBase =>
            pc.pop(Tk.CTimes)
            val right = FunctorProduct.parse(pc)
            pc.pop(Tk.RParen)
            FProduct(base, right)
        }
      case Tk.I => FUnit
      case Tk.LSquare =>
        val tp = PType.parse(pc)
        pc.pop(Tk.RSquare)
        FConstant(tp)
      case Tk.Id => FIdentity
      case _ => throw UnexpectedTokenParseException(tok, "a functor")
    }
  }

  override def equivalent(left: Functor, right: Functor)(ctx: IndexVariableCtx): SubtypingConstraint = {
    (left, right) match
      case (FConstant(l), FConstant(r)) => PType.equivalent(l, r)(ctx)
      case (FIdentity, FIdentity) => SCTrue
      case (FUnit, FUnit) => SCTrue
      case (FProduct(ll, lr), FProduct(rl, rr)) => Functor.equivalent((ll, lr), (rl, rr))(ctx)
      case (FSum(ll, lr), FSum(rl, rr)) => Functor.equivalent((ll, lr), (rl, rr))(ctx)
      case _ => throw TypeException(s"functors are not equivalent: $left ≢ $right")
  }
}
object FunctorSum extends Parseable[FunctorSum] {
  override def parse(pc: ParseContext): FunctorSum = {
    val token = pc.peek()
    Functor.parse(pc) match {
      case sum: FunctorSum => sum
      case _ => throw ParseException("not a sum functor", token.loc)
    }
  }
}
object FunctorProduct extends Parseable[FunctorProduct] {
  override def parse(pc: ParseContext): FunctorProduct = {
    val token = pc.peek()
    Functor.parse(pc) match {
      case prod: FunctorProduct => prod
      case _ => throw ParseException("not a product functor", token.loc)
    }
  }
}
object FunctorBase extends Parseable[FunctorBase] {
  override def parse(pc: ParseContext): FunctorBase = {
    val token = pc.peek()
    Functor.parse(pc) match {
      case base: FunctorBase => base
      case _ => throw ParseException("not a base functor", token.loc)
    }
  }
}

case class FSum(left: FunctorSum, right: FunctorSum) extends FunctorSum {
  override def toString: String = s"($left ⊕ $right)"

  // AlgFunctor⊕
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) & right.wellFormed(ctx)

  // UnrefUnroll⊕
  override def unroll(id: PInductive): PType = PSum(left.unroll(id), right.unroll(id))
}
object FUnit extends FunctorProduct {
  override def toString: String = "I"

  // AlgFunctorI
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = Set.empty

  // UnrefUnrollI
  override def unroll(id: PInductive): PType = PUnit
}
case class FProduct(left: FunctorBase, right: FunctorProduct) extends FunctorProduct {
  override def toString: String = s"($left ⊗ $right)"

  // AlgFunctor⊗
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) | right.wellFormed(ctx)
  
  // UnrefUnrollConst, UnrefUnrollId
  override def unroll(id: PInductive): PType =
    PProd(left match { case FConstant(tp) => tp; case FIdentity => id }, right.unroll(id))
}
case class FConstant(tp: PType) extends FunctorBase {
  override def toString: String = s"[$tp]"

  // AlgFunctorConstant
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    tp.wellFormed(ctx)
}
object FIdentity extends FunctorBase {
  override def toString: String = "Id"

  // AlgFunctorId
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = Set.empty
}
