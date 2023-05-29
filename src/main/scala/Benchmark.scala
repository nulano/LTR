import scala.collection.mutable.ListBuffer

private case class REPLCommandStats(cmd: REPLCommand, start: Long, parsed: Long, done: Long, proofs: Long) {
  val timeToParse: Long = parsed - start
  val timeToCheck: Long = done - parsed
  val timeTotal: Long = done - start
}
private case class FileStats(filename: String, start: Long, done: Long, commands: List[REPLCommandStats]) {
  val timeTotal: Long = done - start
}

private case class SMTStats(assertion: LogicCtx, start: Long, generated: Long, done: Long) {
  val timeToGenerate: Long = generated - start
  val timeToProve: Long = done - generated
  val timeTotal: Long = done - start
}

private object Benchmark {

  var repl = new REPL()
  var fileResults: List[FileStats] = List.empty
  val smtStatsBuf: ListBuffer[SMTStats] = new ListBuffer[SMTStats]

  def run(filename: String): FileStats = {
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
      val proofs_0 = smtStatsBuf.length
      val cmd_start = System.currentTimeMillis()
      val cmd = REPLCommand.parse(repl.makeParseContext(parser))
      val cmd_parsed = System.currentTimeMillis()
      repl.processCommand(cmd)
      val cmd_done = System.currentTimeMillis()
      val proofs_1 = smtStatsBuf.length
      times += REPLCommandStats(cmd, cmd_start, cmd_parsed, cmd_done, proofs_1 - proofs_0)
    }
    val file_t1 = System.currentTimeMillis()
    FileStats(filename, file_t0, file_t1, times.result())
  }

  def benchmarkCallback(ctx: LogicCtx, start: Long, generated: Long, done: Long): Unit = {
    smtStatsBuf += SMTStats(ctx, start, generated, done)
  }

  def main(args: Array[String]): Unit = {
    Z3.debug = false
    Z3.benchmarkCallback = Some(benchmarkCallback)
    collect(run("lib\\boolean.ltr"))
    collect(run("lib\\natural.ltr"))
    collect(run("lib\\list.ltr"))
    collect(FileStats("<all>", 0, fileResults.map(_.timeTotal).sum, fileResults.flatMap(_.commands).toList))

    val smtStats = smtStatsBuf.result()
    val smtSorted = smtStats.sortBy(_.timeToProve)
    val smtGenTimes = smtStats.map(_.timeToGenerate)
    val smtCheckTimes = smtStats.map(_.timeToProve)
    val smtTotalTimes = smtStats.map(_.timeTotal)
    analyze(s"SMT generate", smtGenTimes)
    analyze(s"SMT prove", smtCheckTimes)
    analyze(s"SMT total", smtTotalTimes)
  }

  def collect(fileStats: FileStats): Unit = {
    val parseTimes = fileStats.commands.map(_.timeToParse)
    val checkTimes = fileStats.commands.filter(_.cmd.isInstanceOf[REPLLetCommand]).map(_.timeToCheck)
    val totalTimes = fileStats.commands.map(_.timeTotal)
    analyze(s"${fileStats.filename} parse", parseTimes)
    analyze(s"${fileStats.filename} check", checkTimes)
    analyze(s"${fileStats.filename} total", totalTimes)
    fileResults = fileResults :+ fileStats
  }

  def analyze(title: String, times: List[Long]): Unit = {
    val min = times.min
    val max = times.max
    val avg = 1.0 * times.sum / times.length
    val median = medianCalculator(times)
    val total = times.sum
    val count = times.length
    val stddev = Math.sqrt(times.map(_.toDouble).map(a => math.pow(a - avg, 2)).sum / times.size)
    println(f"$title:\t\t$count\t\ttotal: $total ms\t\tmin: $min ms\t\tavg: $avg%2.2f ± $stddev%2.2f ms\t\tmax: $max ms\t\tmedian: $median ms")
  }

  def medianCalculator(times: List[Long]): Double = {
    val sorted = times.sorted

    if (sorted.size % 2 == 1) sorted(sorted.size / 2)
    else {
      val x = sorted.splitAt(sorted.size / 2)
      (x._1.last + x._2.head) / 2.0
    }
  }
}
