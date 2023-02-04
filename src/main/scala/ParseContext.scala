
sealed case class ParseContext(in: Parser,
                               typeVars: Map[String, TypeVar] = Map(),
                               algebras: Map[String, Algebra] = Map()) {
  def peek(): Token = in.peek()
  def pop(): Token = in.pop()
  def pop(tks: Tk*): Token = in.pop(tks:_*)

  def getTypeVar(token: Token): PType = {
    if token.tk != Tk.Var then
      throw UnexpectedTokenParseException(token, "a type variable")
    else typeVars.unapply(token.text) match
      case Some(value) => value.instantiate(this)
      case None => throw ParseException("type variable is not bound", token.loc)
  }
  
  def getAlgebraVar(token: Token): Algebra = {
    if token.tk != Tk.Var then
      throw UnexpectedTokenParseException(token, "an algebra variable")
    else algebras.unapply(token.text) match
      case Some(value) => value
      case None => throw ParseException("algebra variable is not bound", token.loc)
  }
}

// TODO different file?
case class TypeException(msg: String) extends Exception(msg)

trait Parseable[T] {
  def parse(pc: ParseContext) : T
}
