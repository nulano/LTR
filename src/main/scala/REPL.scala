
sealed trait REPLCommand
sealed trait REPLLetCommand extends REPLCommand {
  def assignment: (String, BoundExpression)
}

object REPLCommand extends Parseable[REPLCommand] {
  override def parse(pc: ParseContext): REPLCommand = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Let =>
        val v = pc.pop(Tk.Var).text
        pc.pop(Tk.Eq)
        val g = BoundExpression.parse(pc)
        REPLLet(v, g)(tok)
      case Tk.Def =>
        val v = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val tp = NType.parse(pc)
        pc.pop(Tk.Eq)
        val e = Expression.parse(pc)
        REPLDef(v, tp, e)(tok)
      case Tk.Rec =>
        val v = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val tp = NType.parse(pc)
        pc.pop(Tk.Eq)
        val e = Expression.parse(pc)
        REPLRec(v, tp, e)(tok)
      case Tk.Alg =>
        val v = pc.pop(Tk.Var).text
        pc.pop(Tk.Eq)
        val a = Algebra.parse(pc)
        REPLAlgebra(v, a)(tok)
      case Tk.Type =>
        val v = pc.pop(Tk.Var).text
        if pc.pop(Tk.Eq, Tk.LParen).tk == Tk.LParen then {
          val i = pc.pop(Tk.Var).text
          pc.pop(Tk.RParen)
          pc.pop(Tk.Eq)
          PType.parse(pc) match
            case tp: PInductive => REPLTypeInductive(v, i, tp)(tok)
            case _ => throw ParseException("expected an inductive type")
        } else {
          val tp = PType.parse(pc)
          REPLType(v, tp)(tok)
        }
      case _ => throw UnexpectedTokenParseException(tok, "a REPL statement")
    }
  }
}

case class REPLLet(variable: String, exp: BoundExpression)(val token: Token) extends REPLLetCommand {
  override def toString: String = s"let $variable = $exp"

  override def assignment: (String, BoundExpression) = (variable, exp)
}
case class REPLDef(variable: String, tp: NType, exp: Expression)(val token: Token) extends REPLLetCommand {
  override def toString: String = s"def $variable : $tp = $exp"

  override def assignment: (String, BoundExpression) =
    (variable, BEExpression(ExpReturn(ValExpression(exp)(token))(token), PSuspended(tp))(token))
}
case class REPLRec(variable: String, tp: NType, exp: Expression)(val token: Token) extends REPLLetCommand {
  override def toString: String = s"rec $variable : $tp = $exp"

  override def assignment: (String, BoundExpression) =
    (variable, BEExpression(ExpReturn(ValExpression(ExpRecursive(variable, tp, exp)(token))(token))(token), PSuspended(tp))(token))
}
case class REPLAlgebra(variable: String, alg: Algebra)(val token: Token) extends REPLCommand {
  override def toString: String = s"alg $variable = $alg"
}
case class REPLType(variable: String, tp: PType)(val token: Token) extends REPLCommand {
  override def toString: String = s"type $variable = $tp"
}
case class REPLTypeInductive(variable: String, indexVariable: String, tp: PInductive)(val token: Token) extends REPLCommand {
  override def toString: String = s"type $variable($indexVariable) = $tp"
}



