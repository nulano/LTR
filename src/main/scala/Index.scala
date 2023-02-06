import scala.annotation.{tailrec, targetName}

trait SubstitutableIndex[T] {
  def substituteIndex(replacement: Index, target: IndexVariable): T
}

sealed trait Index extends SubstitutableIndex[? <: Index] {
  @targetName("substituteFor")
  final def /[T <: SubstitutableIndex[? <: T]](target: IndexVariable)(value: T): T =
    value.substituteIndex(this, target)

  final def sort: Sort = sort(_ => true)
  def sort(ctx: IndexVariable => Boolean): Sort
}
sealed trait IndexBase[T <: IndexBase[T]] extends Index, SubstitutableIndex[T]
sealed trait Proposition extends Index, SubstitutableIndex[? <: Proposition] {
  def checkCanSort(ctx: IndexVariable => Boolean): Unit

  final override def sort(ctx: IndexVariable => Boolean): SBool = { checkCanSort(ctx); SBool() }
}
sealed trait PropositionBase[T <: PropositionBase[T]] extends Proposition, SubstitutableIndex[T]

object Index extends Parseable[Index] {
  override def parse(pc: ParseContext): Index = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var if tok.text == "T" => IPTrue()
      case Tk.Var if tok.text == "F" => IPFalse()
      case Tk.Var => IVariable(pc.getIndexVar(tok))
      case Tk.Number => INatConstant(tok.text.toInt)
      case Tk.Plus => IIntConstant(pc.pop(Tk.Number).text.toInt)
      case Tk.Minus => IIntConstant(-pc.pop(Tk.Number).text.toInt)
      case Tk.PLeft => ILeft(Index.parse(pc))
      case Tk.PRight => IRight(Index.parse(pc))
      case Tk.Not => IPNot(Proposition.parse(pc))
      case Tk.LParen =>
        val left = Index.parse(pc)
        val op = pc.pop(Tk.Plus, Tk.Minus, Tk.Comma, Tk.Eq, Tk.Leq, Tk.And, Tk.Or).tk
        val right = Index.parse(pc)
        pc.pop(Tk.RParen)
        op match {
          case Tk.Plus => ISum(left, right)
          case Tk.Minus => IDifference(left, right)
          case Tk.Comma => IPair(left, right)
          case Tk.Eq => IPEqual(left, right)
          case Tk.Leq => IPLessEqual(left, right)
          case Tk.And | Tk.Or =>
            (left, right) match {
              case (lp: Proposition, rp: Proposition) =>
                if op == Tk.And then IPAnd(lp, rp) else IPOr(lp, rp)
              case _ => throw ParseException("not a proposition")
            }
          case _ => throw AssertionError("unreachable")
        }
      case _ => throw UnexpectedTokenParseException(tok, "an index term")
    }
  }
}

object Proposition extends Parseable[Proposition] {
  override def parse(pc: ParseContext): Proposition =
    Index.parse(pc) match
      case proposition: Proposition => proposition
      case _ => throw ParseException("not a proposition")
}

class IndexVariable(val name: String, val sort: Sort) {
  override def toString: String = s"${name}_${super.hashCode.toHexString} : $sort"
}

object IndexVariable extends Parseable[IndexVariable] {
  override def parse(pc: ParseContext): IndexVariable =
    val name = pc.pop(Tk.Var).text
    pc.pop(Tk.Colon)
    val sort = Sort.parse(pc)
    new IndexVariable(name, sort)
}

case class IVariable(variable: IndexVariable) extends Index, SubstitutableIndex[Index] {
  // hashCode must be 0 to allow for simple α-equivalence of ∀ and ∃ types
  override def hashCode(): Int = 0

  override def toString: String = variable.name

  // IxVar
  override def sort(ctx: IndexVariable => Boolean): Sort =
    if !ctx(variable) then
      throw SortException(this, "variable not in context")
    else variable.sort

  override def substituteIndex(replacement: Index, target: IndexVariable): Index =
    if variable == target then replacement else this
}
case class INatConstant(value: Int) extends IndexBase[INatConstant] {
  if value < 0 then throw new IllegalArgumentException(s"value may not be negative: $value")
  override def toString: String = s"$value"

  // IxConst
  override def sort(ctx: IndexVariable => Boolean): Sort = SNat()

  override def substituteIndex(replacement: Index, target: IndexVariable): INatConstant = this
}
case class IIntConstant(value: Int) extends IndexBase[IIntConstant] {
  override def toString: String = s"$value"

  // IxConst
  override def sort(ctx: IndexVariable => Boolean): Sort = SInt()

  override def substituteIndex(replacement: Index, target: IndexVariable): IIntConstant = this
}
case class ISum(left: Index, right: Index) extends IndexBase[ISum] {
  override def toString: String = s"($left + $right)"

  // IxAdd
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls + $rs")
    ls match
      case SNat() | SInt() => ls
      case _ => throw SortException(this, s"can't perform addition on $ls")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): ISum =
    ISum((replacement / target)(left), (replacement / target)(right))
}
case class IDifference(left: Index, right: Index) extends IndexBase[IDifference] {
  override def toString: String = s"($left - $right)"

  // IxSubtract
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls - $rs")
    ls match
      case SNat() | SInt() => ls
      case _ => throw SortException(this, s"can't perform subtraction on $ls")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IDifference =
    IDifference((replacement / target)(left), (replacement / target)(right))
}
case class IPair(left: Index, right: Index) extends IndexBase[IPair] {
  override def toString: String = s"($left, $right)"

  // IxProd
  override def sort(ctx: IndexVariable => Boolean): Sort =
    SProd(left.sort(ctx), right.sort(ctx))

  override def substituteIndex(replacement: Index, target: IndexVariable): IPair =
    IPair((replacement / target)(left), (replacement / target)(right))
}
case class ILeft(value: Index) extends IndexBase[ILeft] {
  override def toString: String = s"π₁ $value"

  // IxProj1
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    value.sort(ctx) match
      case SProd(left, _) => left
      case s => throw SortException(this, s"can't perform projection on $s")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): ILeft =
    ILeft((replacement / target)(value))
}
case class IRight(value: Index) extends IndexBase[IRight] {
  override def toString: String = s"π₂ $value"

  // IxProj2
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    value.sort(ctx) match
      case SProd(_, right) => right
      case s => throw SortException(this, s"can't perform projection on $s")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IRight =
    IRight((replacement / target)(value))
}
case class IPEqual(left: Index, right: Index) extends PropositionBase[IPEqual] {
  override def toString: String = s"($left = $right)"

  // Ix=
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls = $rs")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IPEqual =
    IPEqual((replacement / target)(left), (replacement / target)(right))
}
case class IPLessEqual(left: Index, right: Index) extends PropositionBase[IPLessEqual] {
  override def toString: String = s"($left ≤ $right)"

  // Ix≤
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls ≤ $rs")
    ls match
      case SNat() | SInt() => ()
      case _ => throw SortException(this, s"can't perform comparison on $ls")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IPLessEqual =
    IPLessEqual((replacement / target)(left), (replacement / target)(right))
}
case class IPAnd(left: Proposition, right: Proposition) extends PropositionBase[IPAnd] {
  override def toString: String = s"($left ∧ $right)"

  // Ix∧
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    left.checkCanSort(ctx)
    right.checkCanSort(ctx)
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IPAnd =
    IPAnd((replacement / target)(left), (replacement / target)(right))
}
case class IPOr(left: Proposition, right: Proposition) extends PropositionBase[IPOr] {
  override def toString: String = s"($left ∨ $right)"

  // Ix∨
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    left.checkCanSort(ctx)
    right.checkCanSort(ctx)
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IPOr =
    IPOr((replacement / target)(left), (replacement / target)(right))
}
case class IPNot(prop: Proposition) extends PropositionBase[IPNot] {
  override def toString: String = s"¬$prop"

  // Ix¬
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = prop.checkCanSort(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): IPNot =
    IPNot((replacement / target)(prop))
}
case class IPTrue() extends PropositionBase[IPTrue] {
  override def toString: String = "T"

  // IxConst
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = ()

  override def substituteIndex(replacement: Index, target: IndexVariable): IPTrue = this
}
case class IPFalse() extends PropositionBase[IPFalse] {
  override def toString: String = "F"

  // IxConst
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = ()

  override def substituteIndex(replacement: Index, target: IndexVariable): IPFalse = this
}
