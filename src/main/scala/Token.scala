import scala.util.matching.Regex

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
  case Plus extends Tk("+")
  case Minus extends Tk("-")
  case Times extends Tk("×")
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
  case Right extends Tk("→")
  case DRight extends Tk("⇒")
  case And extends Tk("∧")
  case Or extends Tk("∨")
  case ForAll extends Tk("∀")
  case Exists extends Tk("∃")
  case Superset extends Tk("⊃")
  case Var extends Tk("<VAR>")

object Tk {
  val regex = new Regex(raw"[ \t\r\n]*+(->|=>|[a-z]++|.)", "token")

  def get(text: String): Tk = text match {
    case "return" => Return
    case "let" => Let
    case "match" => Match
    case "rec" => Rec
    case "inl" | "inj1" | "inj₁" => Inl
    case "inr" | "inj2" | "inj₂" => Inr
    case "into" => Into
    case "." => Dot
    case "," => Comma
    case ":" => Colon
    case ";" => Semicolon
    case "+" => Plus
    case "-" => Minus
    case "×" | "X" => Times
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
    case "→" | "~" | "->" => Right
    case "⇒" | "'" | "=>" => DRight
    case "∧" | "&" => And
    case "∨" | "|" => Or
    case "∀" | "A" => ForAll
    case "∃" | "E" => Exists
    case "⊃" | "S" => Superset
    case _ => Var
  }
}

case class Token(tk: Tk, text: String, loc: ParseLocation)
