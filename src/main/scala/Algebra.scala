import scala.annotation.tailrec
import scala.collection.immutable.VectorBuilder

trait Algebra extends SubstitutableIndex[Algebra] {
  def patterns: Iterable[(AlgebraSumPattern, Index)]

  final override def toString(): String = {
    val body = patterns.map((p, t) => s"$p ⇒ $t").mkString(" ‖ ")
    s"($body)"
  }
}

case class AlgebraSum(left: Algebra, right: Algebra) extends Algebra, SubstitutableIndex[AlgebraSum] {
  override def patterns: Iterable[(AlgebraSumPattern, Index)] =
    left.patterns.map((p, t) => (APLeft(p), t)) ++ right.patterns.map((p, t) => (APRight(p), t))

  override def substituteIndex(replacement: Index, target: IndexVariable): AlgebraSum =
    AlgebraSum((replacement / target)(left), (replacement / target)(right))
}

case class AlgebraProd(pattern: AlgebraProductPattern, index: Index) extends Algebra, SubstitutableIndex[AlgebraProd] {
  override def patterns: Iterable[(AlgebraSumPattern, Index)] = List((pattern, index))

  override def substituteIndex(replacement: Index, target: IndexVariable): AlgebraProd =
    AlgebraProd(pattern, (replacement / target)(index))
}

object Algebra extends Parseable[Algebra] {
  def apply(vector: Vector[(AlgebraSumPattern, Index)]): Algebra = {
    if vector.length > 1 then
      val left = vector.collect{case (lp: APLeft, i: Index) => (lp.pattern, i)}
      val right = vector.collect{case (rp: APRight, i: Index) => (rp.pattern, i)}
      if left.length + right.length != vector.length then
        throw TypeException("conflicting patterns for algebra")
      AlgebraSum(Algebra(left), Algebra(right))
    else if vector.length == 1 then
      val (pat, idx) = vector.head
      pat match
        case prod: AlgebraProductPattern => AlgebraProd(prod, idx)
        case APLeft(_) => throw TypeException("missing right pattern for algebra")
        case APRight(_) => throw TypeException("missing left pattern for algebra")
    else
      throw TypeException("empty algebra is invalid")
  }

  override def parse(pc: ParseContext): Algebra = {
    val tok = pc.pop(Tk.LParen, Tk.Var)
    if tok.tk == Tk.Var then
      pc.getAlgebraVar(tok)
    else /* if pc.peek().tk == Tk.RParen then {
      pc.pop(Tk.RParen)
      Algebra(Vector())
    } else */ {
      val builder = new VectorBuilder[(AlgebraSumPattern, Index)]
      while {
        val p = AlgebraSumPattern.parse(pc)
        pc.pop(Tk.DRight)
        val t = Index.parse(p.extendParseContext(pc))
        builder += ((p, t))
        pc.pop(Tk.DBar, Tk.RParen).tk == Tk.DBar
      } do ()
      Algebra(builder.result())
    }
  }

  /**
   * Check that under valueDetermined ⊆ ctx, algebra (pattern ⇒ index) is well-formed of sort functor(sort) ⇒ sort
   * (assuming functor is well-formed), i.e. Ξ; Θ; Δ ⊢ (p ⇒ t) : F(τ) ⇒ τ (fig. 21b/57b)
   *
   * @param valueDetermined the set of value-determined indexes, i.e. Ξ
   * @param ctx             the set of logic variables that are in context, i.e. Θ ∪ Δ
   * @param pattern         the pattern of the algebra to check, i.e. p
   * @param index           the result of the algebra to check, i.e. t
   * @param functor         the functor to check, i.e. F
   * @param sort            the resulting sort, i.e. τ
   */
  @tailrec
  private def wellFormed(valueDetermined: Set[IndexVariable],
                 ctx: Set[IndexVariable],
                 pattern: AlgebraProductPattern,
                 index: Index,
                 functor: FunctorProduct,
                 sort: Sort): Unit =
    (pattern, functor) match {
      // AlgAlgI
      case (_: APUnit, _: FUnit) =>
        val result = index.sort(valueDetermined)
        if result != sort then
          throw TypeException(s"algebra result is incompatible with requirement: $result != $sort")
      case (alg: APProduct, fun: FProduct) =>
        (alg.left, fun.left) match {
          // AlgAlgId⊗
          case (id: APIdentity, _: FIdentity) =>
            val v = id.variable.withSort(sort)
            wellFormed(valueDetermined + v, ctx + v, alg.right, (IVariable(v) / id.variable)(index), fun.right, sort)
          // AlgAlgConst⊗
          case (_: APConstant, const: FConstant) =>
            const.tp.wellFormed(ctx)
            wellFormed(valueDetermined, ctx, alg.right, index, fun.right, sort)
          // AlgAlgConst∃⊗
          case (pack: APPack, const: FConstant) =>
            const.tp match {
              case exists: PExists =>
                wellFormed(valueDetermined + exists.variable, ctx + exists.variable, APProduct(pack.rest, alg.right),
                  (IVariable(exists.variable) / pack.variable)(index), FProduct(FConstant(exists.tp), fun.right), sort)
              case _ => throw TypeException(s"algebra pattern is incompatible with functor")
            }
          case _ => throw TypeException(s"algebra pattern is incompatible with functor")
        }
      case _ => throw TypeException(s"algebra pattern is incompatible with functor")
    }

  /**
   * Check that under valueDetermined ⊆ ctx, algebra is well-formed of sort functor(sort) ⇒ sort
   * (assuming functor is well-formed), i.e. Ξ; Θ; Δ ⊢ α : F(τ) ⇒ τ (fig. 21b/57b)
   *
   * @param valueDetermined the set of value-determined indexes, i.e. Ξ
   * @param ctx             the set of logic variables that are in context, i.e. Θ ∪ Δ
   * @param algebra         the algebra to check, i.e. α
   * @param functor         the functor to check, i.e. F
   * @param sort            the resulting sort, i.e. τ
   */
  def wellFormed(valueDetermined: Set[IndexVariable],
                 ctx: Set[IndexVariable],
                 algebra: Algebra,
                 functor: Functor,
                 sort: Sort): Unit =
    (algebra, functor) match {
      // AlgAlg⊕
      case (AlgebraSum(la, ra), FSum(lf, rf)) =>
        wellFormed(valueDetermined, ctx, la, lf, sort)
        wellFormed(valueDetermined, ctx, ra, rf, sort)
      case (AlgebraProd(pat, idx), fun: FunctorProduct) =>
        wellFormed(valueDetermined, ctx, pat, idx, fun, sort)
      case _ => throw TypeException(s"algebra is incompatible with functor: $algebra, $functor")
    }
}

sealed trait AlgebraSumPattern {
  def extendParseContext(pc: ParseContext): ParseContext
}
sealed trait AlgebraProductPattern extends AlgebraSumPattern
sealed trait AlgebraBasePattern {
  def extendParseContext(pc: ParseContext): ParseContext
}

object AlgebraSumPattern extends Parseable[AlgebraSumPattern] {
  override def parse(pc: ParseContext): AlgebraSumPattern = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Inl => APLeft(AlgebraSumPattern.parse(pc))
      case Tk.Inr => APRight(AlgebraSumPattern.parse(pc))
      case Tk.LParen =>
        if pc.peek().tk == Tk.RParen then {
          pc.pop(Tk.RParen)
          APUnit()
        } else {
          val left = AlgebraBasePattern.parse(pc)
          pc.pop(Tk.Comma)
          val right = AlgebraProductPattern.parse(pc)
          pc.pop(Tk.RParen)
          APProduct(left, right)
        }
      case _ => throw UnexpectedTokenParseException(tok, "a sum algebra pattern")
    }
  }
}

object AlgebraProductPattern extends Parseable[AlgebraProductPattern] {
  override def parse(pc: ParseContext): AlgebraProductPattern = {
    val tok = pc.peek()
    AlgebraSumPattern.parse(pc) match
      case pattern: AlgebraProductPattern => pattern
      case _ => throw UnexpectedTokenParseException(tok, "a product algebra pattern")
  }
}

object AlgebraBasePattern extends Parseable[AlgebraBasePattern] {
  override def parse(pc: ParseContext): AlgebraBasePattern = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Underscore => APConstant()
      case Tk.Var => APIdentity(new IVPlaceholder(tok.text))
      case Tk.Pack =>
        pc.pop(Tk.LParen)
        val left = IVPlaceholder.parse(pc)
        pc.pop(Tk.Comma)
        val right = AlgebraBasePattern.parse(pc)
        pc.pop(Tk.RParen)
        APPack(left, right)
      case _ => throw UnexpectedTokenParseException(tok, "a base algebra pattern")
    }
  }
}

case class APLeft(pattern: AlgebraSumPattern) extends AlgebraSumPattern {
  override def toString: String = s"inl $pattern"

  override def extendParseContext(pc: ParseContext): ParseContext =
    pattern.extendParseContext(pc)

//  override def substituteIndex(replacement: Index, target: IndexVariable): APLeft =
//    APLeft((replacement / target)(pattern))
}
case class APRight(pattern: AlgebraSumPattern) extends AlgebraSumPattern {
  override def toString: String = s"inr $pattern"

  override def extendParseContext(pc: ParseContext): ParseContext =
    pattern.extendParseContext(pc)

//  override def substituteIndex(replacement: Index, target: IndexVariable): APRight =
//    APRight((replacement / target)(pattern))
}
case class APUnit() extends AlgebraProductPattern {
  override def toString: String = s"()"

  override def extendParseContext(pc: ParseContext): ParseContext = pc

//  override def substituteIndex(replacement: Index, target: IndexVariable): APUnit = this
}
case class APProduct(left: AlgebraBasePattern, right: AlgebraProductPattern) extends AlgebraProductPattern {
  override def toString: String = s"($left, $right)"

  override def extendParseContext(pc: ParseContext): ParseContext =
    right.extendParseContext(left.extendParseContext(pc))

//  override def substituteIndex(replacement: Index, target: IndexVariable): APProduct =
//    APProduct((replacement / target)(left), (replacement / target)(right))
}
case class APConstant() extends AlgebraBasePattern {
  override def toString: String = "_"

  override def extendParseContext(pc: ParseContext): ParseContext = pc

//  override def substituteIndex(replacement: Index, target: IndexVariable): APConstant = this
}
case class APIdentity(variable: IVPlaceholder) extends AlgebraBasePattern {
  // must return zero to preserve α-equality
  override def hashCode(): Int = 0

  override def equals(other: Any): Boolean =
    other match {
      case _: APIdentity => true
      case _ => false
    }

  override def toString: String = variable.name

  override def extendParseContext(pc: ParseContext): ParseContext = pc + variable
}
case class APPack(variable: IVPlaceholder, rest: AlgebraBasePattern) extends AlgebraBasePattern {
  // must ignore variable to preserve α-equality
  override def hashCode(): Int = rest.hashCode

  override def equals(other: Any): Boolean =
    other match {
      case that: APPack => this.rest == that.rest
      case _ => false
    }

  override def toString: String = s"pack(${variable.name}, $rest)"

  override def extendParseContext(pc: ParseContext): ParseContext =
    rest.extendParseContext(pc + variable)
}
