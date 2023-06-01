import scala.collection.immutable.SortedSet

sealed trait Functor extends WellFormed, SubstitutableIndex[Functor]
sealed trait FunctorSum extends Functor, SubstitutableIndex[FunctorSum]
sealed trait FunctorProduct extends FunctorSum, SubstitutableIndex[FunctorProduct]
sealed trait FunctorBase extends Functor, SubstitutableIndex[FunctorBase]

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

case class FSum(left: FunctorSum, right: FunctorSum) extends FunctorSum, SubstitutableIndex[FSum] {
  override def toString: String = s"($left ⊕ $right)"

  // AlgFunctor⊕
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) & right.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): FSum =
    FSum((replacement / target)(left), (replacement / target)(right))

  override def norm: FSum = FSum(left.norm, right.norm)
}
object FUnit extends FunctorProduct, SubstitutableIndex[FUnit.type] {
  override def toString: String = "I"

  // AlgFunctorI
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = SortedSet.empty

  override def substituteIndex(replacement: Index, target: IndexVariable): FUnit.type = FUnit

  override def norm: FUnit.type = FUnit
}
case class FProduct(left: FunctorBase, right: FunctorProduct) extends FunctorProduct, SubstitutableIndex[FProduct] {
  override def toString: String = s"($left ⊗ $right)"

  // AlgFunctor⊗
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    left.wellFormed(ctx) | right.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): FProduct =
    FProduct((replacement / target)(left), (replacement / target)(right))

  override def norm: FProduct = FProduct(left.norm, right.norm)
}
case class FConstant(tp: PType) extends FunctorBase, SubstitutableIndex[FConstant] {
  override def toString: String = s"[$tp]"

  // AlgFunctorConstant
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx =
    tp.wellFormed(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): FConstant =
    FConstant((replacement / target)(tp))

  override def norm: FConstant = FConstant(tp.norm)
}
object FIdentity extends FunctorBase, SubstitutableIndex[FIdentity.type] {
  override def toString: String = "Id"

  // AlgFunctorId
  override def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx = SortedSet.empty

  override def substituteIndex(replacement: Index, target: IndexVariable): FIdentity.type = FIdentity

  override def norm: FIdentity.type = FIdentity
}
