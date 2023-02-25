import scala.annotation.tailrec

sealed trait Expression

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
  def checkType(expression: Expression, tp: NType)(ctx: IndexVariableCtx, vars: VariableContext): Unit = {
    // TODO provide proposition context
    val (te, (ve, pe)) = tp.extract
    val ctx2 = ctx ++ ve
    (expression, te) match
      // Alg⇐↑
      case (ExpReturn(v), NComputation(t)) =>
        val out = Value.checkType(v, t)(ctx2, vars)
        out.foreach(_.check((ctx, List()), vars))  // TODO proposition ctx, simplify
      // Alg⇐let
      case (ExpLet(v, be, bd), _) =>
        val (vte, (vve, vpe)) = be.getType(vars).result.extract
        checkType(bd, te)(ctx2 ++ vve, vars + ((v, vte)))  // TODO vpe
      // Alg⇐match
      case (ExpMatch(h, c), _) =>
        val ht = h.getType(vars)
        MatchPattern.checkType(c, ht, tp)(ctx, vars)
      // Alg⇐λ
      case (ExpFunction(av, be), NFunction(at, bt)) =>
        checkType(be, bt)(ctx2, vars + ((av, at)))
      // Alg⇐rec
      case (ExpRecursive(rv, NForAll(rtv, rtt), rb), _) if rtv.sort == SNat =>
        val ro = NType.subtype(NForAll(rtv, rtt), te)(ctx2)
        ro.check((ctx, List()))  // TODO proposition ctx
        val temp = IVariable(new IVBound(rtv.name, SNat))
        val cond = IPAnd(IPLessEqual(temp, IVariable(rtv)), IPNot(IPEqual(temp, IVariable(rtv))))  // TODO extend syntax?
        val rct = NForAll(temp.variable, NPrecondition(cond, (temp / rtv)(rtt)))
        checkType(rb, rtt)(ctx2 + rtv, vars + ((rv, PSuspended(rct))))
      case _ => throw TypeException(s"expression does not match type: $expression ⇐ $tp")
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

// TODO maybe rename? encapsulates all clauses of a match block
sealed trait MatchPattern

object MatchPattern extends Parseable[MatchPattern] {
  override def parse(pc: ParseContext): MatchPattern = {
    val tok = pc.pop(Tk.LBrace)
    val tok2 = pc.pop()
    tok2.tk match {
      case Tk.RBrace => MPVoid()(tok)
      case Tk.LAngle => {
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
      }
      case Tk.Inl => {
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
      }
      case Tk.Inr => {
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
      }
      case Tk.Into => {
        pc.pop(Tk.LParen)
        val variable = pc.pop(Tk.Var).text
        pc.pop(Tk.RParen)
        pc.pop(Tk.DRight)
        val body = Expression.parse(pc)
        pc.pop(Tk.RBrace)
        MPInto(variable, body)(tok)
      }
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
  def checkType(pattern: MatchPattern, arg: PType, tp: NType)(ctx: IndexVariableCtx, vars: VariableContext): Unit = {
    (pattern, arg) match {
      // AlgMatch∃
      case (_, pe: PExists) =>
        checkType(pattern, pe.tp, tp)(ctx + pe.variable, vars)
      // AlgMatch∧
      case (_, pp: PProperty) =>
        // TODO pp.proposition
        checkType(pattern, pp.tp, tp)(ctx, vars)
      // AlgMatch1
      case (mpu: MPUnit, PUnit) =>
        Expression.checkType(mpu.body, tp)(ctx, vars)
      // AlgMatch×
      case (mpp: MPProd, pp: PProd) =>
        val (ae, (av, ap)) = pp.left.extract
        val (be, (bv, bp)) = pp.right.extract
        // TODO ap + bp
        Expression.checkType(mpp.body, tp)(ctx ++ av ++ bv, vars + ((mpp.left, ae)) + ((mpp.right, be)))
      // AlgMatch+
      case (mps: MPSum, ps: PSum) =>
        val (ae, (av, ap)) = ps.left.extract
        val (be, (bv, bp)) = ps.right.extract
        // TODO ap, bp
        Expression.checkType(mps.leftBody, tp)(ctx ++ av, vars + ((mps.left, ae)))
        Expression.checkType(mps.rightBody, tp)(ctx ++ bv, vars + ((mps.right, be)))
      // AlgMatch0
      case (_: MPVoid, PVoid) => ()
      // AlgMatchμ
      case (mpi: MPInto, pi: PInductive) =>
        val (ae, (av, ap)) = pi.unroll.extract
        // TODO ap
        Expression.checkType(mpi.body, tp)(ctx ++ av, vars + ((mpi.variable, ae)))
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


