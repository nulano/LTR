import java.io.{BufferedReader, InputStreamReader}
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
    case IProduct(left, right) => s"(* ${convert(left)} ${convert(right)})"
    case IDivision(left, right) =>
      val i = IndexVariableCounter.next
      val rv = s"right$i"
      // TODO returns 0 if divisor is 0
      s"(let (($rv ${convert(right)})) (ite (= $rv 0) 0 (div ${convert(left)} $rv)))"
    case IRemainder(left, right) =>
      val i = IndexVariableCounter.next
      val rv = s"right$i"
      // TODO returns 0 if divisor is 0
      s"(let (($rv ${convert(right)})) (ite (= $rv 0) 0 (mod ${convert(left)} $rv)))"
    case IPair(left, right) => s"(pair ${convert(left)} ${convert(right)})"
    case ILeft(value) => s"(fst ${convert(value)})"
    case IRight(value) => s"(snd ${convert(value)})"
    case IPEqual(left, right) => s"(= ${convert(left)} ${convert(right)})"
    case IPNotEqual(left, right) => s"(distinct ${convert(left)} ${convert(right)})"
    case IPLess(left, right) => s"(< ${convert(left)} ${convert(right)})"
    case IPLessEqual(left, right) => s"(<= ${convert(left)} ${convert(right)})"
    case IPGreater(left, right) => s"(> ${convert(left)} ${convert(right)})"
    case IPGreaterEqual(left, right) => s"(>= ${convert(left)} ${convert(right)})"
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
  private val process = new ProcessBuilder("z3", "-in").start()
  private val processInput = process.getOutputStream
  private val processOutput = new BufferedReader(new InputStreamReader(process.getInputStream))
  
  type BenchmarkCallback = (String, Boolean, Long, Long) => Unit

  var debug = true
  var benchmarkCallback: Option[BenchmarkCallback] = None

  processInput.write("(set-option :timeout 1000)\n".getBytes)

  private def assertUnsat(ctx: LogicCtx, statement: String, trivial: Boolean): Unit = {
    if debug then
      System.err.println(s"Z3 checking: $statement")
    val (isUnsat, timeToGenerate, timeToProve) = unsat(ctx)
    if !isUnsat then
      throw TypeException(s"failed to verify: $statement")
    benchmarkCallback.foreach(_(statement, trivial, timeToGenerate, timeToProve))
  }

  def assert(ctx: LogicCtx, proposition: Proposition): Unit = {
    val trivial = proposition match {
      case IPTrue => return
      case IPEqual(a, b) => a == b
      case _ => false
    }
    assertUnsat(ctx + IPNot(proposition), s"$ctx ⊨ $proposition", trivial)
  }

  def assertEqual(ctx: LogicCtx, left: Proposition, right: Proposition): Unit = {
    assertUnsat(ctx + IPNotEqual(left, right), s"$ctx ⊨ $left ≡ $right", left == right)
  }

  def assertUnsat(ctx: LogicCtx): Unit = assertUnsat(ctx, s"$ctx ⊨ F", false)

  /**
   * Check that ctx is unsatisfiable, i.e. that its negation is valid.
   * @param ctx the logic context to check
   * @return tuple of three values:
   *         (true if ctx is not satisfiable, false otherwise;
   *         time taken to generate SMT-LIB file;
   *         time taken by Z3)
   */
  def unsat(ctx: LogicCtx): (Boolean, Long, Long) = {
    val time_start = System.currentTimeMillis()
    val text = SMTLIBGenerator.generate(ctx).mkString("", "\n", "\n(reset)\n")
    val time_generated = System.currentTimeMillis()
    processInput.write(text.getBytes)
    processInput.flush()
    val output = processOutput.readLine()
    val time_done = System.currentTimeMillis()
    if output == null || !process.isAlive then
      throw new RuntimeException("Z3 process died")
    // TODO "unknown" -> timeout
    //      "sat" -> not unsat
    (output.trim == "unsat", time_generated - time_start, time_done - time_generated)
  }
}
