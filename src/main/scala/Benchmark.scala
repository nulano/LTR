import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.{ArrayBuffer, ListBuffer}

private object Benchmark {

  private case class REPLCommandStats(cmd: REPLCommand, start: Long, parsed: Long, done: Long, smtBefore: Int, smtAfter: Int) {
    val timeToParse: Long = parsed - start
    val timeToCheck: Long = done - parsed
    val timeTotal: Long = done - start

    def timeSmt: Long = {
      smtStatsBuf.slice(smtBefore, smtAfter).map(_.timeTotal).sum
    }
  }

  private case class FileStats(filename: String, start: Long, done: Long, commands: List[REPLCommandStats]) {
    val timeTotal: Long = done - start
  }

  private case class SMTStats(statement: String, trivial: Boolean, timeToGenerate: Long, timeToProve: Long) {
    val timeTotal: Long = timeToGenerate + timeToProve
  }

  private val repl = new REPL()
  private var fileResults: List[FileStats] = List.empty
  private val smtStatsBuf: ArrayBuffer[SMTStats] = new ArrayBuffer[SMTStats]
  private val texTable: ListBuffer[String] = new ListBuffer[String]

  private def run(filename: String): FileStats = {
    val file = new java.io.File(filename)
    if !file.isFile then
      throw new ParseException(s"file not found: $file")
    val source = scala.io.Source.fromFile(file, "utf-8")
    val reader = try
      val text = source.mkString
      text.split(raw"\n\r?").iterator
    finally
      source.close()
    val parser = new Parser(filename, reader)
    val times = new ListBuffer[REPLCommandStats]
    val file_t0 = System.currentTimeMillis()
    while parser.peek().tk != Tk.EOF do {
      val proofs_0 = smtStatsBuf.size
      val cmd_start = System.currentTimeMillis()
      val cmd = REPLCommand.parse(repl.makeParseContext(parser))
      val cmd_parsed = System.currentTimeMillis()
      repl.processCommand(cmd)
      val cmd_done = System.currentTimeMillis()
      val proofs_1 = smtStatsBuf.size
      times += REPLCommandStats(cmd, cmd_start, cmd_parsed, cmd_done, proofs_0, proofs_1)
    }
    val file_t1 = System.currentTimeMillis()
    FileStats(filename, file_t0, file_t1, times.result())
  }

  def main(args: Array[String]): Unit = {
    Z3.debug = false
    Z3.benchmarkCallback = Some((a, b, c, d) => smtStatsBuf += SMTStats(a, b, c, d))
    collect(run("lib\\boolean.ltr"))
    collect(run("lib\\natural.ltr"))
    collect(run("lib\\list.ltr"))
    collect(FileStats("<all>", 0, fileResults.map(_.timeTotal).sum, fileResults.flatMap(_.commands)))

    val smtSorted = smtStatsBuf.sortBy(_.timeToProve).toList
    val smtGenTimes = smtSorted.map(_.timeToGenerate)
    val smtCheckTimes = smtSorted.map(_.timeToProve)
    val smtTotalTimes = smtSorted.map(_.timeTotal)
    val smtTotalTimesNontrivial = smtSorted.filterNot(_.trivial).map(_.timeTotal)
    analyze("SMT", "generate", smtGenTimes)
    analyze("SMT", "prove", smtCheckTimes)
    analyze("SMT", "total", smtTotalTimes)
    analyze("SMT", "nontrivial", smtTotalTimesNontrivial)
    println("\n5 slowest SMT proofs:")
    println(smtSorted.takeRight(5).reverse.map(s => s"${s.timeToProve}ms: ${s.statement}").mkString("\n"))
    println("\nIn LaTeX format:")
    texTable.foreach(println(_))
  }

  private def collect(fileStats: FileStats): Unit = {
    val parseTimes = fileStats.commands.map(_.timeToParse)
    val checkTimes = fileStats.commands.filter(_.cmd.isInstanceOf[REPLLetCommand]).map(_.timeToCheck)
    val nonSmtTimes = fileStats.commands.filter(_.cmd.isInstanceOf[REPLLetCommand]).map(s => s.timeToCheck - s.timeSmt)
    val totalTimes = fileStats.commands.map(_.timeTotal)
    analyze(fileStats.filename, "parse", parseTimes)
    analyze(fileStats.filename, "check", checkTimes)
    analyze(fileStats.filename, "check - SMT", nonSmtTimes)
    analyze(fileStats.filename, "total", totalTimes)
    fileResults = fileResults :+ fileStats
  }

  def analyze(group: String, title: String, times: List[Long]): Unit = {
    val min = times.min
    val max = times.max
    val avg = 1.0 * times.sum / times.length
//    val median = medianCalculator(times)
    val total = times.sum
    val count = times.length
    val stddev = Math.sqrt(times.map(_.toDouble).map(a => math.pow(a - avg, 2)).sum / times.size)
    println(f"$group $title:\t\t$count\t\ttotal: $total ms\t\tmin: $min ms\t\tavg: $avg%2.2f ± $stddev%2.2f ms\t\tmax: $max ms")
    texTable += f"$group%-15s & $title%-11s &$$$count%3d$$&$$$total%4d ms$$&$$$min%2d ms$$&$$$avg%4.2f±$stddev%4.2f ms$$&$$$max%3d ms$$\\\\"
  }

//  def medianCalculator(times: List[Long]): Double = {
//    val sorted = times.sorted
//
//    if (sorted.size % 2 == 1) sorted(sorted.size / 2)
//    else {
//      val x = sorted.splitAt(sorted.size / 2)
//      (x._1.last + x._2.head) / 2.0
//    }
//  }
}
