import scala.annotation.tailrec

sealed trait Expression {
  val token: Token
}

object Expression extends Parseable[Expression] {
  override def parse(pc: ParseContext): Expression = {
    val tok = pc.pop()
    tok.tk match {
      case Tk.Return => ExpReturn(Value.parse(pc))(tok)
      case Tk.Let =>
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Eq)
        val bound = BoundExpression.parse(pc)
        pc.pop(Tk.Semicolon)
        val body = Expression.parse(pc)
        ExpLet(variable, bound, body)(tok)
      case Tk.Match =>
        val head = Head.parse(pc)
        val clauses = MatchPattern.parse(pc)
        ExpMatch(head, clauses)(tok)
      case Tk.Lambda =>
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpFunction(variable, body)(tok)
      case Tk.Rec =>
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.Colon)
        val tp = NType.parse(pc)
        pc.pop(Tk.Dot)
        val body = Expression.parse(pc)
        ExpRecursive(variable, tp, body)(tok)
      case Tk.Unreachable => ExpUnreachable()(tok)
      case _ => throw UnexpectedTokenParseException(tok, "an expression")
    }
  }

  /**
   * Check expression matches tp, i.e. `Θ; Γ ▷ expression ⇐ tp'` (fig. 66b)
   * @param expression the expression to check
   * @param tp the type to check
   * @param ctx the index variable context, i.e. Θ
   * @param vars the variable context, i.e. Γ
   */
  @tailrec
  def checkType(expression: Expression, tp: NType)(ctx: LogicCtx, vars: VariableContext): Unit = {
    val (te, tc) = tp.extract
    val ctx2 = ctx ++ tc
    (expression, te) match
      // Alg⇐↑
      case (ExpReturn(v), NComputation(t)) =>
        val out = Value.checkType(v, t)(ctx2.idxVars, vars)
        out.foreach(c => {
          try c.check(ctx2, vars)
          catch
            case typeException: TypeException =>
              throw TypeException(expression.token.loc.caused(s"type constraint $c unsatisfied in expression $expression")).initCause(typeException)
        })
      // Alg⇐let
      case (ExpLet(v, be, bd), _) =>
        val (vt, vc) = be.getType(ctx2, vars).result.extract
        checkType(bd, te)(ctx2 ++ vc, vars + ((v, vt)))
      // Alg⇐match
      case (ExpMatch(h, c), _) =>
        val ht = h.getType(ctx2, vars)
        MatchPattern.checkType(c, ht, tp)(ctx2, vars)
      // Alg⇐λ
      case (ExpFunction(av, be), NFunction(at, bt)) =>
        checkType(be, bt)(ctx2, vars + ((av, at)))
      // Alg⇐rec
      case (ExpRecursive(rv, NForAll(rtv, rtt), rb), _) if rtv.sort == SNat =>
        NType.subtype(NForAll(rtv, rtt), te)(ctx2.idxVars).check(ctx2)
        val temp = IVariable(new IVBound(rtv.name, SNat))
        val cond = IPLess(temp, IVariable(rtv))
        val rct = PSuspended(NForAll(temp.variable, NPrecondition(cond, (temp / rtv)(rtt))))
        checkType(rb, rtt)(ctx2 + rtv, vars + ((rv, rct)))
      case (ExpUnreachable(), _) =>
        Z3.assertUnsat(ctx)
      case _ => throw TypeException(expression.token.loc.caused(s"expression does not match type: $expression ⇐ $tp"))
  }
}

case class ExpReturn(value: Value)(val token: Token) extends Expression {
  override def toString: String = s"return $value"
}
case class ExpLet(variable: String, value: BoundExpression, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"let $variable = $value; $body"
}
case class ExpMatch(head: Head, clauses: MatchPattern)(val token: Token) extends Expression {
  override def toString: String = s"match $head $clauses"
}
case class ExpFunction(variable: String, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"λ$variable . $body"
}
case class ExpRecursive(variable: String, tp: NType, body: Expression)(val token: Token) extends Expression {
  override def toString: String = s"rec $variable : $tp . $body"
}
case class ExpUnreachable()(val token: Token) extends Expression {
  override def toString: String = "unreachable"
}

// TODO maybe rename? encapsulates all clauses of a match block
sealed trait MatchPattern

object MatchPattern extends Parseable[MatchPattern] {
  override def parse(pc: ParseContext): MatchPattern = {
    val tok = pc.pop(Tk.LBrace)
    val tok2 = pc.pop()
    tok2.tk match {
      case Tk.RBrace => MPVoid()(tok)
      case Tk.LAngle =>
        if pc.peek().tk == Tk.RAngle then {
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          MPUnit(body)(tok)
        } else {
          val left = pc.pop(Tk.Var).text
          pc.pop(Tk.Comma)
          val right = pc.pop(Tk.Var).text
          pc.pop(Tk.RAngle)
          pc.pop(Tk.DRight)
          val body = Expression.parse(pc)
          pc.pop(Tk.RBrace)
          MPProd(left, right, body)(tok)
        }
      case Tk.Inl =>
        val left = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val leftBody = Expression.parse(pc)
        pc.pop(Tk.DBar)
        pc.pop(Tk.Inr)
        val right = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val rightBody = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPSum(left, leftBody, right, rightBody)(tok)
      case Tk.Inr =>
        val right = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val rightBody = Expression.parse(pc)
        pc.pop(Tk.DBar)
        pc.pop(Tk.Inl)
        val left = pc.pop(Tk.Var).text
        pc.pop(Tk.DRight)
        val leftBody = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPSum(left, leftBody, right, rightBody)(tok)
      case Tk.Into =>
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        pc.pop(Tk.DRight)
        val body = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPInto(variable, body)(tok)
      case _ => throw UnexpectedTokenParseException(tok2, "a match pattern")
    }
  }

  /**
   * Check match pattern matches arg with output tp, i.e. `Θ; Γ [arg] ▷ pattern ⇐ tp'` (fig. 67a)
   *
   * @param pattern the pattern to check
   * @param arg the argument to check
   * @param tp the type to check
   * @param ctx the index variable context, i.e. Θ
   * @param vars the variable context, i.e. Γ
   */
  @tailrec
  def checkType(pattern: MatchPattern, arg: PType, tp: NType)(ctx: LogicCtx, vars: VariableContext): Unit = {
    (pattern, arg) match {
      // AlgMatch∃
      case (_, pe: PExists) =>
        checkType(pattern, pe.tp, tp)(ctx + pe.variable, vars)
      // AlgMatch∧
      case (_, pp: PProperty) =>
        checkType(pattern, pp.tp, tp)(ctx + pp.proposition, vars)
      // AlgMatch1
      case (mpu: MPUnit, PUnit) =>
        Expression.checkType(mpu.body, tp)(ctx, vars)
      // AlgMatch×
      case (mpp: MPProd, pp: PProd) =>
        val (ae, ac) = pp.left.extract
        val (be, bc) = pp.right.extract
        Expression.checkType(mpp.body, tp)(ctx ++ ac ++ bc, vars + ((mpp.left, ae)) + ((mpp.right, be)))
      // AlgMatch+
      case (mps: MPSum, ps: PSum) =>
        val (ae, ac) = ps.left.extract
        val (be, bc) = ps.right.extract
        Expression.checkType(mps.leftBody, tp)(ctx ++ ac, vars + ((mps.left, ae)))
        Expression.checkType(mps.rightBody, tp)(ctx ++ bc, vars + ((mps.right, be)))
      // AlgMatch0
      case (_: MPVoid, PVoid) => ()
      // AlgMatchμ
      case (mpi: MPInto, pi: PInductive) =>
        val (ue, uc) = pi.unroll.extract
        Expression.checkType(mpi.body, tp)(ctx ++ uc, vars + ((mpi.variable, ue)))
      case _ => throw TypeException(s"match pattern does not match argument type: $pattern, $arg")
    }
  }
}

case class MPVoid()(val token: Token) extends MatchPattern {
  override def toString: String = "{}"
}

case class MPInto(variable: String, body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{into($variable) ⇒ $body}"
}
case class MPUnit(body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{<> ⇒ $body}"
}
case class MPProd(left: String, right: String, body: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{<$left, $right> ⇒ $body}"
}
case class MPSum(left: String, leftBody: Expression, right: String, rightBody: Expression)(val token: Token) extends MatchPattern {
  override def toString: String = s"{inl $left ⇒ $leftBody ‖ inr $right ⇒ $rightBody}"
}


