import scala.annotation.{tailrec, targetName}
import scala.collection.immutable.SortedSet

trait SubstitutableIndex[+T] {
  /**
   * Substitute replacement for target in this.
   * @param replacement the substituted index term
   * @param target the index variable to be substituted
   * @return the result, i.e. [replacement / target]this
   */
  def substituteIndex(replacement: Index, target: IndexVariable): T

  /**
   * Perform algorithmic variable substitution.
   * @return This term with all solved algorithmic variables replaced with their solution, i.e. [Δ]this.
   */
  def norm: T
}

type IndexVariableCtx = SortedSet[IndexVariable]
type PropositionCtx = List[Proposition]
case class LogicCtx(idxVars: IndexVariableCtx, propositions: PropositionCtx) {
  @targetName("incl")
  inline def +(variable: IndexVariable): LogicCtx = LogicCtx(idxVars + variable, propositions)

  @targetName("incl")
  inline def +(proposition: Proposition): LogicCtx = LogicCtx(idxVars, proposition +: propositions)

  @targetName("concat")
  inline def ++(other: LogicCtx): LogicCtx =
    LogicCtx(idxVars ++ other.idxVars, propositions ++ other.propositions)

  override def toString: String = (idxVars, propositions) match {
    case (s, Nil) if s.isEmpty => "∙"
    case (_, Nil) => idxVars.mkString("(", ", ", ")")
    case (s, _) if s.isEmpty => propositions.mkString("(", ", ", ")")
    case (_, _) => s"(${idxVars.mkString(", ")}, ${propositions.mkString(", ")})"
  }
}
object LogicCtx {
  val empty: LogicCtx = LogicCtx(SortedSet.empty, List.empty)
}

trait Extracts[T <: Extracts[T]] {
  /**
   * Extract variables and propositions from type, i.e. this ⇝ (T, Θ) (fig. 29/61).
   * @return extracted type and logic context, i.e. (T, Θ)
   */
  def extract: (T, LogicCtx)
}

trait WellFormed {
  /**
   * Check that under ctx, this is well-formed, returning value-determined indexes,
   * i.e. Θ; Δ ⊢ this [Ξ] (figs. 20/56, 21a/57a)
   * @param ctx the set of logic variables that are in context, i.e. Θ ∪ Δ
   * @return the set of value-determined indexes, i.e. Ξ
   */
  def wellFormed(ctx: IndexVariableCtx): IndexVariableCtx
}

sealed trait Index extends SubstitutableIndex[Index] {
  @targetName("substituteFor")
  final def /[T <: SubstitutableIndex[T]](target: IndexVariable)(value: T): T =
    value.substituteIndex(this, target)

  /**
   * Determine the sort of this under any context, i.e. * ⊢ this : τ (fig. 18/54)
   * @return the set of value-determined indexes, i.e. τ
   */
  final def sort: Sort = sort(_ => true)

  /**
   * Determine the sort of this under ctx, i.e. Θ; Δ ⊢ this : τ (fig. 18/54)
   * @param ctx the set of logic variables that are in context, i.e. Θ ∪ Δ
   * @return the set of value-determined indexes, i.e. τ
   */
  def sort(ctx: IndexVariable => Boolean): Sort

  /**
   * Check whether this index has no free variables,
   * i.e. that <code>this.sort(_ => false)</code> does not throw a SortException.
   * @return true if this term has no free variables, false otherwise
   */
  final def isGround: Boolean =
    try
      sort(!_.isInstanceOf[IVAlgorithmic]); true  // TODO other vars are OK???
    catch case _: SortException => false
}
sealed trait IndexBase[T <: IndexBase[T]] extends Index, SubstitutableIndex[T]
sealed trait Proposition extends Index, SubstitutableIndex[Proposition] {
  def checkCanSort(ctx: IndexVariable => Boolean): Unit

  final override def sort(ctx: IndexVariable => Boolean): SBool.type = { checkCanSort(ctx); SBool }
}
sealed trait PropositionBase[T <: PropositionBase[T]] extends Proposition, SubstitutableIndex[T]

object Index extends Parseable[Index] {
  override def parse(pc: ParseContext): Index = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Top => IPTrue
      case Tk.Bottom => IPFalse
      case Tk.Var => IVariable(pc.getIndexVar(tok))
      case Tk.Number => INatConstant(tok.text.toInt)
      case Tk.Plus => IIntConstant(pc.pop(Tk.Number).text.toInt)
      case Tk.Minus => IIntConstant(-pc.pop(Tk.Number).text.toInt)
      case Tk.PLeft => ILeft(Index.parse(pc))
      case Tk.PRight => IRight(Index.parse(pc))
      case Tk.Not => IPNot(Proposition.parse(pc))
      case Tk.LParen =>
        val left = Index.parse(pc)
        val op = pc.pop(Tk.Plus, Tk.Minus, Tk.Star, Tk.Slash, Tk.Percent, Tk.Comma,
                        Tk.Eq, Tk.Ne, Tk.LAngle, Tk.RAngle, Tk.Leq, Tk.Geq, Tk.And, Tk.Or).tk
        val right = Index.parse(pc)
        pc.pop(Tk.RParen)
        op match {
          case Tk.Plus => ISum(left, right)
          case Tk.Minus => IDifference(left, right)
          case Tk.Star => IProduct(left, right)
          case Tk.Slash => IDivision(left, right)
          case Tk.Percent => IRemainder(left, right)
          case Tk.Comma => IPair(left, right)
          case Tk.Eq => IPEqual(left, right)
          case Tk.Ne => IPNotEqual(left, right)
          case Tk.LAngle => IPLess(left, right)
          case Tk.RAngle => IPGreater(left, right)
          case Tk.Leq => IPLessEqual(left, right)
          case Tk.Geq => IPGreaterEqual(left, right)
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

case class IVariable(variable: IndexVariable) extends Index {
  // hashCode must be 0 to allow for simple α-equivalence of ∀ and ∃ types
  override def hashCode(): Int = 0

  override def toString: String = s"${variable.name}${IndexVariableCounter.toString(variable.number)}"

  // IxVar
  override def sort(ctx: IndexVariable => Boolean): Sort =
    if !ctx(variable) then
      throw SortException(this, "variable not in context")
    else variable.sort

  override def substituteIndex(replacement: Index, target: IndexVariable): Index =
    if variable == target then replacement else this

  override def norm: Index =
    variable match
      case algorithmic: IVAlgorithmic =>
        algorithmic.solution match
          case Some(value) => value.norm
          case None => this
      case _ => this
}
case class INatConstant(value: Int) extends IndexBase[INatConstant] {
  if value < 0 then throw new IllegalArgumentException(s"value may not be negative: $value")
  override def toString: String = s"$value"

  // IxConst
  override def sort(ctx: IndexVariable => Boolean): SNat.type = SNat

  override def substituteIndex(replacement: Index, target: IndexVariable): INatConstant = this

  override def norm: INatConstant = this
}
case class IIntConstant(value: Int) extends IndexBase[IIntConstant] {
  override def toString: String = f"$value%+d"

  // IxConst
  override def sort(ctx: IndexVariable => Boolean): SInt.type = SInt

  override def substituteIndex(replacement: Index, target: IndexVariable): IIntConstant = this

  override def norm: IIntConstant = this
}
private sealed trait INumeric[T <: INumeric[T]] extends IndexBase[T] {
  val left: Index
  val right: Index
  val op: String

  def copy(left: Index, right: Index): T

  override def toString: String = s"($left $op $right)"

  // IxAdd, IxSubtract
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls $op $rs")
    ls match
      case SNat | SInt => ls
      case _ => throw SortException(this, s"can't perform $op on $ls")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): T =
    copy((replacement / target)(left), (replacement / target)(right))

  override def norm: T = copy(left.norm, right.norm)
}
case class ISum(left: Index, right: Index) extends INumeric[ISum] { val op: String = "+" }
case class IDifference(left: Index, right: Index) extends INumeric[IDifference] { val op: String = "-"}
case class IProduct(left: Index, right: Index) extends INumeric[IProduct] { val op: String = "*" }
case class IDivision(left: Index, right: Index) extends INumeric[IDivision] { val op: String = "/" }
case class IRemainder(left: Index, right: Index) extends INumeric[IRemainder] { val op: String = "%" }
case class IPair(left: Index, right: Index) extends IndexBase[IPair] {
  override def toString: String = s"($left, $right)"

  // IxProd
  override def sort(ctx: IndexVariable => Boolean): SProd =
    SProd(left.sort(ctx), right.sort(ctx))

  override def substituteIndex(replacement: Index, target: IndexVariable): IPair =
    IPair((replacement / target)(left), (replacement / target)(right))

  override def norm: IPair = IPair(left.norm, right.norm)
}
case class ILeft(value: Index) extends IndexBase[ILeft] {
  override def toString: String = s"L $value"

  // IxProj1
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    value.sort(ctx) match
      case SProd(left, _) => left
      case s => throw SortException(this, s"can't perform projection on $s")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): ILeft =
    ILeft((replacement / target)(value))

  override def norm: ILeft = ILeft(value.norm)
}
case class IRight(value: Index) extends IndexBase[IRight] {
  override def toString: String = s"R $value"

  // IxProj2
  override def sort(ctx: IndexVariable => Boolean): Sort = {
    value.sort(ctx) match
      case SProd(_, right) => right
      case s => throw SortException(this, s"can't perform projection on $s")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IRight =
    IRight((replacement / target)(value))

  override def norm: IRight = IRight(value.norm)
}
private sealed trait IPBinary[T <: IPBinary[T]] extends PropositionBase[T] {
  val left: Index
  val right: Index
  val op: String

  def copy(left: Index, right: Index): T

  override def toString: String = s"($left $op $right)"

  // Ix=
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    val ls = left.sort(ctx)
    val rs = right.sort(ctx)
    if ls != rs then
      throw SortException(this, s"sort mismatch: $ls $op $rs")
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): T =
    copy((replacement / target)(left), (replacement / target)(right))

  override def norm: T = copy(left.norm, right.norm)
}
private sealed trait IPNumeric[T <: IPNumeric[T]] extends IPBinary[T] {
  // Ix≤
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    // TODO avoid checking sort twice - exponential behaviour
    left.sort(ctx) match
      case SNat | SInt => super.checkCanSort(ctx)
      case ls => throw SortException(this, s"can't perform numeric comparison on $ls")
  }
}
case class IPEqual(left: Index, right: Index) extends IPBinary[IPEqual] { val op: String = "=" }
case class IPNotEqual(left: Index, right: Index) extends IPBinary[IPNotEqual] { val op: String = "≠" }
case class IPLess(left: Index, right: Index) extends IPNumeric[IPLess] { val op: String = "<" }
case class IPLessEqual(left: Index, right: Index) extends IPNumeric[IPLessEqual] { val op: String = "≤" }
case class IPGreater(left: Index, right: Index) extends IPNumeric[IPGreater] { val op: String = ">" }
case class IPGreaterEqual(left: Index, right: Index) extends IPNumeric[IPGreaterEqual] { val op: String = "≥" }
case class IPAnd(left: Proposition, right: Proposition) extends PropositionBase[IPAnd] {
  override def toString: String = s"($left ∧ $right)"

  // Ix∧
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = {
    left.checkCanSort(ctx)
    right.checkCanSort(ctx)
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): IPAnd =
    IPAnd((replacement / target)(left), (replacement / target)(right))

  override def norm: IPAnd = IPAnd(left.norm, right.norm)
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

  override def norm: IPOr = IPOr(left.norm, right.norm)
}
case class IPNot(prop: Proposition) extends PropositionBase[IPNot] {
  override def toString: String = s"¬$prop"

  // Ix¬
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = prop.checkCanSort(ctx)

  override def substituteIndex(replacement: Index, target: IndexVariable): IPNot =
    IPNot((replacement / target)(prop))

  override def norm: IPNot = IPNot(prop.norm)
}
object IPTrue extends PropositionBase[IPTrue.type] {
  override def toString: String = "T"

  // IxConst
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = ()

  override def substituteIndex(replacement: Index, target: IndexVariable): IPTrue.type = this

  override def norm: IPTrue.type = this
}
object IPFalse extends PropositionBase[IPFalse.type] {
  override def toString: String = "F"

  // IxConst
  override def checkCanSort(ctx: IndexVariable => Boolean): Unit = ()

  override def substituteIndex(replacement: Index, target: IndexVariable): IPFalse.type = this

  override def norm: IPFalse.type = this
}
