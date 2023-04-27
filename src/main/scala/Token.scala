import scala.util.matching.Regex

enum Tk(val text: String):
  case Return extends Tk("return")
  case Let extends Tk("let")
  case Match extends Tk("match")
  case Rec extends Tk("rec")
  case Def extends Tk("def")
  case Alg extends Tk("alg")
  case Type extends Tk("type")
  case Unreachable extends Tk("unreachable")
  case Inl extends Tk("inl")
  case Inr extends Tk("inr")
  case PLeft extends Tk("π₁")
  case PRight extends Tk("π₂")
  case Into extends Tk("into")
  case Pack extends Tk("pack")
  case I extends Tk("I")
  case Id extends Tk("Id")
// TODO
//  case Min extends Tk("min")
//  case Max extends Tk("max")
//  case Abs extends Tk("abs")
  case Underscore extends Tk("_")
  case Dot extends Tk(".")
  case Comma extends Tk(",")
  case Colon extends Tk(":")
  case Semicolon extends Tk(";")
  case Plus extends Tk("+")
  case Minus extends Tk("-")
  case Star extends Tk("*")
  case Slash extends Tk("/")
  case Percent extends Tk("%")
  case Times extends Tk("×")
  case CPlus extends Tk("⊕")
  case CTimes extends Tk("⊗")
  case Eq extends Tk("=")
  case Ne extends Tk("≠")
  case Leq extends Tk("≤")
  case Geq extends Tk("≥")
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
  case Not extends Tk("¬")
  case ForAll extends Tk("∀")
  case Exists extends Tk("∃")
  case Superset extends Tk("⊃")
  case Top extends Tk("⊤")
  case Bottom extends Tk("⊥")
  case Boolean extends Tk("𝔹")
  case Natural extends Tk("ℕ")
  case Integer extends Tk("ℤ")
  case Comment extends Tk("<COMMENT>")
  case Number extends Tk("<NUM>")
  case Var extends Tk("<VAR>")
  case Invalid extends Tk("<INVALID>")
  case EOF extends Tk("<EOF>")

object Tk {
  private val numberRegex = new Regex("^[0-9]+$")
  val regex = new Regex(raw"[ \t\r\n]*+((?:inj|π)[12₁₂]|Id|\([+×X]\)|[<>!]=|[-=]>|\|\||--|[0-9]++|[a-z][a-zA-Z0-9_]*+|.)", "token")

  def get(text: String): Tk = text match {
    case "return" => Return
    case "let" => Let
    case "match" => Match
    case "rec" => Rec
    case "def" => Def
    case "alg" => Alg
    case "type" => Type
    case "unreachable" => Unreachable
    case "inl" | "inj1" | "inj₁" => Inl
    case "inr" | "inj2" | "inj₂" => Inr
    case "L" | "π1" | "π₁" => PLeft
    case "R" | "π2" | "π₂" => PRight
    case "into" => Into
    case "pack" => Pack
    case "I" => I
    case "Id" | "id" => Id
// TODO
//    case "min" => Min
//    case "max" => Max
//    case "abs" => Abs
    case "_" => Underscore
    case "." => Dot
    case "," => Comma
    case ":" => Colon
    case ";" => Semicolon
    case "+" => Plus
    case "-" => Minus
    case "*" => Star
    case "/" => Slash
    case "%" => Percent
    case "×" | "X" => Times
    case "⊕" | "(+)" => CPlus
    case "⊗" | "(×)" | "(X)" => CTimes
    case "=" => Eq
    case "≠" | "!=" => Ne
    case "≤" | "<=" => Leq
    case "≥" | ">=" => Geq
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
    case "¬" | "!" => Not
    case "∀" | "A" => ForAll
    case "∃" | "E" => Exists
    case "⊃" | "S" => Superset
    case "⊤" | "T" => Top
    case "⊥" | "F" => Bottom
    case "𝔹" | "B" => Boolean
    case "ℕ" | "N" => Natural
    case "ℤ" | "Z" => Integer
    case "--" | "#" => Comment
    case _ if numberRegex.matches(text) => Number
    case _ if ('a' <= text.charAt(0) && text.charAt(0) <= 'z') => Var
    case _ => Invalid
  }
}
