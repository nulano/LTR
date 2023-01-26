import scala.collection.mutable

private def isIdentifierChar(c: Character): Boolean = {
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".contains(c)
}

case class ParseException(msg: String) extends Exception(msg)

// TODO different file?
case class TypeException(msg: String) extends Exception(msg)

sealed trait ParseContext {
  def peek() : Token
  def pop() : Token
  def pop(tk: Tk*) : Token = {
    val tok = pop()
    if !tk.contains(tok.tk) then throw ParseException(s"unexpected '${tok.text}' (expecting '${tk.map(_.text).mkString("' or '")}')")
    tok
  }
}

trait Parseable[T] {
  def parse(pc: ParseContext) : T
}

class QueueParseContext(val queue : mutable.Queue[String]) extends ParseContext {
  private var index = 0

  private def check(): Unit = {
    if queue.isEmpty then throw ParseException("unexpected EOF")
  }

  private def makeToken(text: String, loc: Int): Token = {
    Token(Tk.get(text), text, IntLocation(loc))
  }

  override def peek(): Token = { check(); makeToken(queue.front, index) }
  override def pop(): Token = { val tok = peek(); index += 1; tok }
}

class StringParseContext(val text: String) extends ParseContext {
  private var index = 0

  private def skipWhitespace(): Unit = {
    while index < text.length & " \t\n\r".contains(text.charAt(index)) do index += 1
  }

  private def readWord(): String = {
    if !isIdentifierChar(text.charAt(index)) then text.substring(index, index + 1) else {
      var end = index + 1
      while end < text.length & isIdentifierChar(text.charAt(end)) do end += 1
      text.substring(index, end)
    }
  }

  override def peek(): Token = {
    skipWhitespace()
    if index >= text.length then throw ParseException("unexpected EOF")
    val word = readWord()
    Token(Tk.get(word), word, IntLocation(index))
  }

  override def pop(): Token = {
    val tok = peek()
    index += tok.text.length
    tok
  }
}
