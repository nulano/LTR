
class REPL {
  var ctx: LogicCtx = LogicCtx.empty
  var vars: VariableContext = Map()
  var typeVars: Map[String, TypeVar] = Map()
  var algebras: Map[String, Algebra] = Map()

  def makeParseContext(parser: Parser): ParseContext = {
    ParseContext(parser, typeVars = typeVars, algebras = algebras)
  }

  def processCommand(cmd: REPLCommand): String = {
    cmd match
      case command: REPLLetCommand =>
        val (tp, c) = command.boundExpression.getType(ctx, vars).result.extract
        this.ctx = this.ctx ++ c
        this.vars = this.vars + ((command.variable, tp))
        s"let ${command.variable} : $tp"
      case REPLAlgebra(variable, alg) =>
        this.algebras = this.algebras + ((variable, AlgebraNamed(alg, variable)))
        cmd.toString
      case REPLType(variable, tp) =>
        this.typeVars = this.typeVars + ((variable, TVConstant(tp)))
        cmd.toString
      case REPLTypeInductive(variable, indexVariable, tp) =>
        this.typeVars = this.typeVars + ((variable, TVInductive(indexVariable, tp)))
        cmd.toString
  }
}

sealed trait REPLCommand
sealed trait REPLLetCommand extends REPLCommand {
  val variable: String
  def boundExpression: BoundExpression
}
sealed trait REPLLetValCommand extends REPLLetCommand {
  val tp: PType
  val value: Value
  val token: Token

  override def boundExpression: BoundExpression = BEExpression(ExpReturn(value)(token), tp)(token)
}

object REPLCommand extends Parseable[REPLCommand] {
  override def parse(pc: ParseContext): REPLCommand = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Let =>
        val v = pc.pop(Tk.Var).text
        if pc.pop(Tk.Eq, Tk.Colon).tk == Tk.Eq then
          val g = BoundExpression.parse(pc)
          REPLLet(v, g)(tok)
        else
          val tp = PType.parse(pc)
          pc.pop(Tk.Eq)
          val value = Value.parse(pc)
          REPLLetVal(v, tp, value)(tok)
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
        if pc.pop(Tk.Eq, Tk.LParen).tk == Tk.LParen then
          val i = IVBound.parse(pc)
          pc.pop(Tk.RParen)
          pc.pop(Tk.Eq)
          REPLTypeInductive(v, i, PType.parse(pc + i))(tok)
        else
          val tp = PType.parse(pc)
          REPLType(v, tp)(tok)
      case _ => throw UnexpectedTokenParseException(tok, "a REPL statement")
    }
  }
}

case class REPLLet(override val variable: String, override val boundExpression: BoundExpression)(val token: Token) extends REPLLetCommand {
  override def toString: String = s"let $variable = $boundExpression"
}
case class REPLLetVal(override val variable: String, override val tp: PType, override val value: Value)(override val token: Token) extends REPLLetValCommand {
  override def toString: String = s"let $variable : $tp = $value"
}
case class REPLDef(override val variable: String, ntp: NType, exp: Expression)(override val token: Token) extends REPLLetValCommand {
  override def toString: String = s"def $variable : $ntp = $exp"

  override val tp: PType = PSuspended(ntp)
  override val value: Value = ValExpression(exp)(token)
}
case class REPLRec(override val variable: String, ntp: NType, exp: Expression)(override val token: Token) extends REPLLetValCommand {
  override def toString: String = s"rec $variable : $ntp = $exp"

  override val tp: PType = PSuspended(ntp)
  override val value: Value = ValExpression(ExpRecursive(variable, ntp, exp)(token))(token)
}
case class REPLAlgebra(variable: String, alg: Algebra)(val token: Token) extends REPLCommand {
  override def toString: String = s"alg $variable = $alg"
}
case class REPLType(variable: String, tp: PType)(val token: Token) extends REPLCommand {
  override def toString: String = s"type $variable = $tp"
}
// TODO rename
case class REPLTypeInductive(variable: String, indexVariable: IndexVariable, tp: PType)(val token: Token) extends REPLCommand {
  override def toString: String = s"type $variable($indexVariable) = $tp"
}

sealed trait TypeVar {
  def instantiate(pc: ParseContext): PType
}

case class TVConstant(tp: PType) extends TypeVar {
  override def instantiate(pc: ParseContext): PType = tp
}

// TODO check index variable scope
// TODO rename
case class TVInductive(variable: IndexVariable, tp: PType) extends TypeVar {
  override def instantiate(pc: ParseContext): PType = {
    val tok = pc.pop(Tk.LParen)
    val idx = Index.parse(pc)
    pc.pop(Tk.RParen)
    try
      val idx_sort = idx.sort
      if idx_sort != variable.sort then
        throw SortException(idx, s"argument has wrong type $idx_sort (expected ${variable.sort})")
    catch
      case tex: TypeException =>
        val pex = new ParseException(tex.getMessage, Some(tok.loc))
        pex.initCause(tex)
        throw pex
    (idx / variable)(tp)
  }
}

