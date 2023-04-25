import scala.collection.mutable.ListBuffer
import scala.language.postfixOps

object SMTLIBGenerator {
  private def convert(variable: IndexVariable): String =
    s"${variable.name}${variable.number}"

  private def convert(sort: Sort): String = sort match
    case SBool => "Bool"
    case SNat => "Int"  // ℕ not supported, add separate assertions and special-case subtraction
    case SInt => "Int"
    case SProd(left, right) => s"(Pair ${convert(left)} ${convert(right)})"

  private def convert(index: Index): String = index match {
    case IVariable(variable) => convert(variable)
    case INatConstant(value) => value.toString
    case IIntConstant(value) => value.toString
    case ISum(left, right) => s"(+ ${convert(left)} ${convert(right)})"
    case IDifference(left, right) =>
      if left.sort == SNat then
        val i = IndexVariableCounter.next
        val lv = s"left$i"
        val rv = s"right$i"
        s"(let (($lv ${convert(left)}) ($rv ${convert(right)})) (ite (>= $lv $rv) (- $lv $rv) 0))"
      else
        s"(- ${convert(left)} ${convert(right)})"
    case IPair(left, right) => s"(pair ${convert(left)} ${convert(right)})"
    case ILeft(value) => s"(fst ${convert(value)})"
    case IRight(value) => s"(snd ${convert(value)})"
    case IPEqual(left, right) => s"(= ${convert(left)} ${convert(right)})"
    case IPLessEqual(left, right) => s"(<= ${convert(left)} ${convert(right)})"
    case IPAnd(left, right) => s"(and ${convert(left)} ${convert(right)})"
    case IPOr(left, right) => s"(or ${convert(left)} ${convert(right)})"
    case IPNot(value) => s"(not ${convert(value)})"
    case IPTrue => "true"
    case IPFalse => "false"
  }

  private def markNatural(sort: Sort, term: String): List[String] = sort match {
    case SBool => List.empty
    case SNat => List(s"(assert (>= $term 0))")
    case SInt => List.empty
    case SProd(left, right) =>
      // TODO performance of returning lists?
      markNatural(left, s"(fst $term)") ++ markNatural(right, s"(snd $term)")
  }

  private def declareVariable(indexVariable: IndexVariable): List[String] = {
    val variable = convert(indexVariable)
    val sort = indexVariable.sort
    val decl = s"(declare-const $variable ${convert(sort)})"
    decl +: markNatural(sort, variable)
  }

  private def assert(proposition: Proposition): String =
    s"(assert ${convert(proposition)})"

  def generate(ctx: LogicCtx): List[String] = {
    ctx.propositions.foreach(_.sort(ctx.idxVars)) // check consistency

    val out = ListBuffer[String]()

    out.addOne("(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (fst X) (snd Y))))))")
    out.addAll(ctx.idxVars.toSeq.flatMap(declareVariable))
    out.addAll(ctx.propositions.map(assert))
    out.addOne("(check-sat)")

    out.result()
  }
}

object Z3 {
  /**
   * Check that ctx is unsatisfiable, i.e. that its negation is valid.
   * @param ctx the logic context to check
   * @return true if ctx is not satisfiable, false otherwise
   */
  def unsat(ctx: LogicCtx): Boolean = {
    val text = SMTLIBGenerator.generate(ctx).mkString("\n")
    val input: java.io.InputStream = new java.io.ByteArrayInputStream(text.getBytes)
    val process = scala.sys.process.Process("z3 -in")
    val output = process #< input !!;
    output.trim == "unsat"
  }
}
