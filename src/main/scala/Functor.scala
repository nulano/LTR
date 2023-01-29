
sealed trait Functor
sealed trait FunctorSum extends Functor {
  def unroll(id: PInductive): PType
}
sealed trait FunctorProduct extends FunctorSum
sealed trait FunctorBase extends Functor

object Functor extends Parseable[Functor] {
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
      case Tk.I => FUnit()
      case Tk.LSquare =>
        val tp = PType.parse(pc)
        pc.pop(Tk.RSquare)
        FConstant(tp)
      case Tk.Id => FIdentity()
      case _ => throw UnexpectedTokenParseException(tok, "a functor")
    }
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

  // UnrefUnroll⊕
  override def unroll(id: PInductive): PType = PSum(left.unroll(id), right.unroll(id))
}
case class FUnit() extends FunctorProduct {
  override def toString: String = "I"

  // UnrefUnrollI
  override def unroll(id: PInductive): PType = PUnit()
}
case class FProduct(left: FunctorBase, right: FunctorProduct) extends FunctorProduct {
  override def toString: String = s"($left ⊗ $right)"

  // UnrefUnrollConst, UnrefUnrollId
  override def unroll(id: PInductive): PType =
    PProd(left match { case FConstant(tp) => tp; case FIdentity() => id }, right.unroll(id))
}
case class FConstant(tp: PType) extends FunctorBase {
  override def toString: String = s"[$tp]"
}
case class FIdentity() extends FunctorBase {
  override def toString: String = "Id"
}
