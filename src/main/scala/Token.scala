
enum Tk(val text: String):
  case Return extends Tk("return")
  case Let extends Tk("let")
  case Match extends Tk("match")
  case Rec extends Tk("rec")
  case Inl extends Tk("inl")
  case Inr extends Tk("inr")
  case Into extends Tk("into")
  case Dot extends Tk(".")
  case Comma extends Tk(",")
  case Colon extends Tk(":")
  case Semicolon extends Tk(";")
  case Eq extends Tk("=")
  case LParen extends Tk("(")
  case RParen extends Tk(")")
  case LBrace extends Tk("{")
  case RBrace extends Tk("}")
  case LAngle extends Tk("<")
  case RAngle extends Tk(">")
  case LSquare extends Tk("[")
  case RSquare extends Tk("]")
  case Lambda extends Tk("λ")
  case Up extends Tk("↑")
  case Down extends Tk("↓")
  case Var extends Tk("<VAR>")

object Tk {
  def get(text: String): Tk = text match {
    case "return" => Return
    case "let" => Let
    case "match" => Match
    case "rec" => Rec
    case "inl" | "inj1" => Inl
    case "inr" | "inj2" => Inr
    case "into" => Into
    case "." => Dot
    case "," => Comma
    case ":" => Colon
    case ";" => Semicolon
    case "=" => Eq
    case "(" => LParen
    case ")" => RParen
    case "{" => LBrace
    case "}" => RBrace
    case "<" => LAngle
    case ">" => RAngle
    case "[" => LSquare
    case "]" => RSquare
    case "λ" | "fun" => Lambda
    case "↑" | "^" => Up
    case "↓" | "V" => Down
    case _ => Var
  }
}

trait Location
case class IntLocation(loc: Int) extends Location

case class Token(tk: Tk, text: String, loc: Location)
