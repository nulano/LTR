import scala.collection.mutable.ListBuffer

sealed trait Head {
  /**
   * Compute synthesized type, i.e. `Θ; Γ ▷ this ⇒ P` (fig. 65a)
   * @param ctx the logic context, i.e. Θ
   * @param vars the variable context, i.e. Γ
   * @return the synthesized type, i.e. P
   */
  def getType(ctx: LogicCtx, vars: VariableContext): PType
}

object Head extends Parseable[Head] {
  override def parse(pc: ParseContext): Head = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Var => HeadVariable(tok.text)(tok)
      case Tk.LSquare =>
        val v = Value.parse(pc)
        pc.pop(Tk.Colon)
        val tp = PType.parse(pc)
        pc.pop(Tk.RSquare)
        HeadValue(v, tp)(tok)
      case _ => throw UnexpectedTokenParseException(tok, "a head")
    }
  }
}

case class HeadVariable(variable: String)(val token: Token) extends Head {
  override def toString: String = variable

  // Alg⇒Var
  override def getType(ctx: LogicCtx, vars: VariableContext): PType =
    vars.get(variable) match
      case Some(value) => value
      case None => throw TypeException(s"unbound variable $variable")
}
case class HeadValue(value: Value, tp: PType)(val token: Token) extends Head {
  override def toString: String = s"[$value : $tp]"

  // Alg⇒ValAnnot
  override def getType(ctx: LogicCtx, vars: VariableContext): PType = {
    tp.wellFormed(ctx.idxVars)
    val out = Value.checkType(value, tp)(ctx.idxVars, vars)
    out.foreach(_.check(ctx, vars)) // TODO simplify
    tp
  }
}

sealed trait BoundExpression {
  /**
   * Compute synthesized type, i.e. `Θ; Γ ▷ this ⇒ ↑P` (fig. 65b)
   * @param ctx  the logic context, i.e. Θ
   * @param vars the variable context, i.e. Γ
   * @return the synthesized type, i.e. ↑P
   */
  def getType(ctx: LogicCtx, vars: VariableContext): NComputation
}

object BoundExpression extends Parseable[BoundExpression] {
  override def parse(pc: ParseContext): BoundExpression = {
    val tok = pc.peek()
    if tok.tk == Tk.LParen then {
      pc.pop(Tk.LParen)
      val exp = Expression.parse(pc)
      pc.pop(Tk.Colon)
      pc.pop(Tk.Up)
      val tp = PType.parse(pc)
      pc.pop(Tk.RParen)
      BEExpression(exp, tp)(tok)
    } else {
      val head = Head.parse(pc)  // TODO custom exception?
      pc.pop(Tk.LParen)
      val spine = ListBuffer[Value]()
      if pc.peek().tk == Tk.RParen then {
        pc.pop(Tk.RParen)
      } else {
        spine += Value.parse(pc)
        while pc.pop(Tk.Comma, Tk.RParen).tk == Tk.Comma do
          spine += Value.parse(pc)
      }
      BEApplication(head, spine.result())(tok)
    }
  }
}

case class BEApplication(head: Head, spine: List[Value])(val token: Token) extends BoundExpression {
  override def toString: String = s"$head(${spine.mkString(",")})"

  // Alg⇒App
  override def getType(ctx: LogicCtx, vars: VariableContext): NComputation = {
    head.getType(ctx, vars) match
      case PSuspended(headType) =>
        val (res, const) = BEApplication.applySpine(headType, spine)(ctx.idxVars, vars)
        const.foreach(_.check(ctx, vars)) // TODO simplify
        NComputation(res)
      case headType => throw TypeException(s"type '$headType' is not a suspended computation")
  }
}
object BEApplication {
  private def applySpine(head: NType, spine: List[Value])(ctx: IndexVariableCtx, vars: VariableContext): (PType, List[TypingConstraint]) = {
    (head, spine) match
      // AlgSpine∀
      case (nfa: NForAll, _) =>
        val temp = new IVAlgorithmic(nfa.variable)
        val (res, const) = applySpine((IVariable(temp) / nfa.variable)(nfa.tp), spine)(ctx + temp, vars)
        if temp.solution.isEmpty then
          throw TypeException(s"failed to determine algorithmic variable $temp in $head")
        (res, const)
      // AlgSpine⊃
      case (np: NPrecondition, _) =>
        val (ot, oc) = applySpine(np.tp, spine)(ctx, vars)
        (ot, SCProposition(np.proposition) :: oc)
      // AlgSpineApp
      case (nf: NFunction, v :: s) =>
        val a = Value.checkType(v, nf.arg)(ctx, vars)
        val (t, b) = applySpine(nf.body.norm, s)(ctx, vars)  // TODO nf.body.norm here is needed for Tp≡⁺/⊣μ and <:⁺/⊣μ, test well!!!
        (t, a ++ b)
      // AlgSpineNil
      case (nc: NComputation, Nil) =>
        (nc.result, Nil)
      case _ => throw TypeException(s"head type does not match spine: $head(${spine.mkString(", ")})")
  }
}
case class BEExpression(exp: Expression, tp: PType)(val token: Token) extends BoundExpression {
  val resultType: NComputation = NComputation(tp)

  override def toString: String = s"($exp : $resultType)"

  // Alg⇒ExpAnnot
  override def getType(ctx: LogicCtx, vars: VariableContext): NComputation = {
    tp.wellFormed(ctx.idxVars)
    Expression.checkType(exp, resultType)(ctx, vars)
    resultType
  }
}
