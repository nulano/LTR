import scala.collection.immutable.VectorBuilder

case class Algebra(patterns: Vector[(AlgebraSumPattern, Index)]) extends SubstitutableIndex[Algebra] {
  override def toString(): String = {
    val body = patterns.map((p, t) => s"$p ⇒ $t").mkString(" ‖ ")
    s"($body)"
  }

  override def substituteIndex(replacement: Index, target: IndexVariable): Algebra =
    Algebra(patterns.map((p, i) => (p, (replacement / target)(i))))
}

object Algebra extends Parseable[Algebra] {
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
case class APIdentity(variable: IndexVariable) extends AlgebraBasePattern {
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
case class APPack(variable: IndexVariable, rest: AlgebraBasePattern) extends AlgebraBasePattern {
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
