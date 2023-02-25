
object IndexVariableCounter {
  private var count: Int = 0
  def next: Int = {
    val out = count
    count += 1
    out
  }
  def toString(i: Int): String = i.toString.map(c => (c - '0' + '₀').toChar)
}

trait IndexVariable {
  def name: String
  def sort: Sort
  def number: Int
}

class IVBound(val name: String, val sort: Sort) extends IndexVariable {
  val number: Int = IndexVariableCounter.next
  override def toString: String = s"$name${IndexVariableCounter.toString(number)} : $sort"
}

object IVBound extends Parseable[IndexVariable] {
  override def parse(pc: ParseContext): IVBound =
    val name = pc.pop(Tk.Var).text
    pc.pop(Tk.Colon)
    val sort = Sort.parse(pc)
    new IVBound(name, sort)
}

class IVAlgorithmic(val variable: IndexVariable) extends IndexVariable {
  val number: Int = IndexVariableCounter.next
  var solution: Option[Index] = None
  override def name: String = variable.name.patch(1, "\u0302", 0)
  override def sort: Sort = variable.sort
  override def toString: String = s"$name${IndexVariableCounter.toString(number)} : $sort"
}

class IVPlaceholder(val name: String) extends IndexVariable {
  val number: Int = IndexVariableCounter.next
  override def sort: Sort = throw new IllegalStateException("placeholder variable has no sort")

  def withSort(sort: Sort): IVBound = new IVBound(name, sort)

  override def toString: String = s"$name${IndexVariableCounter.toString(number)} : ?"
}

object IVPlaceholder extends Parseable[IVPlaceholder] {
  override def parse(pc: ParseContext): IVPlaceholder =
    val name = pc.pop(Tk.Var).text
    new IVPlaceholder(name)
}
