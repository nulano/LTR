import scala.util.matching.Regex

enum Tk(val text: String):
  case Return extends Tk("return")
  case Let extends Tk("let")
  case Match extends Tk("match")
  case Rec extends Tk("rec")
  case Inl extends Tk("inl")
  case Inr extends Tk("inr")
  case Into extends Tk("into")
  case I extends Tk("I")
  case Id extends Tk("Id")
  case Dot extends Tk(".")
  case Comma extends Tk(",")
  case Colon extends Tk(":")
  case Semicolon extends Tk(";")
  case Plus extends Tk("+")
  case Minus extends Tk("-")
  case Times extends Tk("×")
  case CPlus extends Tk("⊕")
  case CTimes extends Tk("⊗")
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
  case Mu extends Tk("μ")
  case Up extends Tk("↑")
  case Down extends Tk("↓")
  case Right extends Tk("→")
  case DRight extends Tk("⇒")
  case DBar extends Tk("‖")
  case And extends Tk("∧")
  case Or extends Tk("∨")
  case ForAll extends Tk("∀")
  case Exists extends Tk("∃")
  case Superset extends Tk("⊃")
  case Boolean extends Tk("𝔹")
  case Natural extends Tk("ℕ")
  case Integer extends Tk("ℤ")
  case Var extends Tk("<VAR>")

object Tk {
  val regex = new Regex(raw"[ \t\r\n]*+(inj[12₁₂]|Id|\([+×X]\)|->|=>|\|\||[a-z]++|.)", "token")

  def get(text: String): Tk = text match {
    case "return" => Return
    case "let" => Let
    case "match" => Match
    case "rec" => Rec
    case "inl" | "inj1" | "inj₁" => Inl
    case "inr" | "inj2" | "inj₂" => Inr
    case "into" => Into
    case "I" => I
    case "Id" | "id" => Id
    case "." => Dot
    case "," => Comma
    case ":" => Colon
    case ";" => Semicolon
    case "+" => Plus
    case "-" => Minus
    case "×" | "X" => Times
    case "⊕" | "(+)" => CPlus
    case "⊗" | "(×)" | "(X)" => CTimes
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
    case "μ" | "fix" => Mu
    case "↑" | "^" => Up
    case "↓" | "V" => Down
    case "→" | "~" | "->" => Right
    case "⇒" | "'" | "=>" => DRight
    case "‖" | "||" => DBar
    case "∧" | "&" => And
    case "∨" | "|" => Or
    case "∀" | "A" => ForAll
    case "∃" | "E" => Exists
    case "⊃" | "S" => Superset
    case "𝔹" | "B" => Boolean
    case "ℕ" | "N" => Natural
    case "ℤ" | "Z" => Integer
    case _ => Var
  }
}

case class Token(tk: Tk, text: String, loc: ParseLocation)
