import scala.util.matching.Regex

case class Token(tk: Tk, text: String, loc: ParseLocation)

sealed trait ParseLocation {
  def caused(msg: String): String = s"msg, at $this"
}

class ParseException(val msg: String, val loc: Option[ParseLocation] = None)
  extends Exception(loc.fold(msg)(_.caused(msg))) {
}

object ParseException {
  def apply(msg: String) = new ParseException(msg, None)

  def apply(msg: String, loc: ParseLocation) = new ParseException(msg, Some(loc))
}

case class EOFException() extends ParseException("unexpected EOF")

class UnexpectedTokenParseException(val token: Token, val expected: String)
  extends ParseException(s"unexpected '${token.text}' (expecting $expected)", Some(token.loc))

object UnexpectedTokenParseException {
  def apply(token: Token, expected: String) = new UnexpectedTokenParseException(token, expected)
}

private val causedRegex = new Regex(raw"[^ \t]")

sealed class Parser(name: String, lines: Iterator[String]) {
  private var row: Int = 0
  private var col: Int = 0
  private var line: String = ""
  private var current: Option[Token] = None

  case class Location(line: String, row: Int, col: Int, len: Int) extends ParseLocation {
    override def toString: String = s"$name:$row:${col + 1}"

    override def caused(msg: String): String = {
      val prefix = causedRegex.replaceAllIn(line.substring(0, col), " ")
      s"$msg, at $this\n    $line\n    $prefix${"^" * len}"
    }
  }

  private def next(): Token = {
    Tk.regex.findPrefixMatchOf(line.substring(col)) match
      case None =>
        try
          line = lines.next()
          row += 1
          col = 0
          this.next()
        catch
          case _: NoSuchElementException =>
            Token(Tk.EOF, "<end-of-file>", Location(line, row, col, 4))
      case Some(m) =>
        val word = m.group(1)
        Tk.get(word) match
          case Tk.Comment =>
            col = line.length
            this.next()
          case tk =>
            val loc = Location(line, row, col + m.start(1), word.length)
            col += m.end(0)
            Token(tk, word, loc)
  }

  def peek(): Token = current match {
    case Some(value) => value
    case None =>
      val value = this.next()
      current = Some(value)
      value
  }

  def pop(): Token = {
    val token = this.peek()
    current = None
    token
  }

  def pop(tks: Tk*): Token = {
    val token = this.pop()
    if !tks.contains(token.tk) then
      throw UnexpectedTokenParseException(token, s"'${tks.map(_.text).mkString("' or '")}'")
    token
  }
}

object Parser {
  def forString(name: String, text: String): Parser =
    new Parser(name, text.split(raw"\r\n|[\r\n]").iterator)
}
