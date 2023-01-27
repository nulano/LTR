//import scala.collection.mutable

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

class UnexpectedTokenParseException(val token: Token, val expected: String)
  extends ParseException(s"unexpected '${token.text}' (expecting $expected)", Some(token.loc))

object UnexpectedTokenParseException {
  def apply(token: Token, expected: String) = new UnexpectedTokenParseException(token, expected)
}

// TODO different file?
case class TypeException(msg: String) extends Exception(msg)

sealed trait ParseContext {
  def peek() : Token
  def pop() : Token
  def pop(tk: Tk*) : Token = {
    val tok = pop()
    if !tk.contains(tok.tk) then
      throw UnexpectedTokenParseException(tok, s"'${tk.map(_.text).mkString("' or '")}'")
    tok
  }
}

trait Parseable[T] {
  def parse(pc: ParseContext) : T
}

//class QueueParseContext(val queue : mutable.Queue[String]) extends ParseContext {
//  private var index = 0
//
//  private def check(): Unit = {
//    if queue.isEmpty then throw ParseException("unexpected EOF")
//  }
//
//  private def makeToken(text: String, loc: Int): Token = {
//    Token(Tk.get(text), text, IntLocation(loc))
//  }
//
//  override def peek(): Token = { check(); makeToken(queue.front, index) }
//  override def pop(): Token = { val tok = peek(); index += 1; tok }
//}

class StringParseContext(val text: String) extends ParseContext {
  private var index = 0

  private case class StringLocation(start: Int, end: Int) extends ParseLocation {
    val length: Int = end - start

    override def toString: String = s"input:${start + 1}"

    override def caused(msg: String): String =
      s"$msg, at $this\n    $text\n    ${" " * start}${"^" * length}"
  }

  override def peek(): Token = {
    Tk.regex.findPrefixMatchOf(text.substring(index)) match
      case None => throw ParseException("unexpected EOF", StringLocation(index, text.length + 4))
      case Some(m) => {
        val word = m.group(1)
        val loc = StringLocation(index + m.start(1), index + m.end(1))
        Token(Tk.get(word), word, loc)
      }
  }

  override def pop(): Token = {
    val tok = peek()
    index = tok.loc.asInstanceOf[StringLocation].end
    tok
  }
}
