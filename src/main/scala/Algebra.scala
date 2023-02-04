import scala.collection.immutable.VectorBuilder

case class Algebra(patterns: Vector[(AlgebraSumPattern, Index)]) {
  override def toString(): String = {
    val body = patterns.map((p, t) => s"$p ⇒ $t").mkString(" ‖ ")
    s"($body)"
  }
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
        val t = Index.parse(pc)
        builder.addOne((p, t))
        pc.pop(Tk.DBar, Tk.RParen).tk == Tk.DBar
      } do ()
      Algebra(builder.result())
    }
  }
}

sealed trait AlgebraSumPattern
sealed trait AlgebraProductPattern extends AlgebraSumPattern
sealed trait AlgebraBasePattern

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
      case Tk.Var => APIdentity(tok.text)
      case Tk.Pack =>
        pc.pop(Tk.LParen)
        val left = pc.pop(Tk.Var).text
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
}
case class APRight(pattern: AlgebraSumPattern) extends AlgebraSumPattern {
  override def toString: String = s"inr $pattern"
}
case class APUnit() extends AlgebraProductPattern {
  override def toString: String = s"()"
}
case class APProduct(left: AlgebraBasePattern, right: AlgebraProductPattern) extends AlgebraProductPattern {
  override def toString: String = s"($left, $right)"
}
case class APConstant() extends AlgebraBasePattern {
  override def toString: String = "_"
}
case class APIdentity(name: String) extends AlgebraBasePattern {
  override def toString: String = name
}
case class APPack(name: String, rest: AlgebraBasePattern) extends AlgebraBasePattern {
  override def toString: String = s"pack($name, $rest)"
}
