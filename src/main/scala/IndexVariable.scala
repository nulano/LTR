
trait IndexVariable {
  def name: String
  def sort: Sort
}

class IVBound(val name: String, val sort: Sort) extends IndexVariable {
  override def toString: String = s"${name}_${super.hashCode.toHexString} : $sort"
}

object IVBound extends Parseable[IndexVariable] {
  override def parse(pc: ParseContext): IVBound =
    val name = pc.pop(Tk.Var).text
    pc.pop(Tk.Colon)
    val sort = Sort.parse(pc)
    new IVBound(name, sort)
}

class IVAlgorithmic(val variable: IndexVariable) extends IndexVariable {
  override def name: String = variable.name.patch(1, "\u0302", 0)
  override def sort: Sort = variable.sort
  override def toString: String = s"${name}_${super.hashCode.toHexString} : $sort"
}

class IVPlaceholder(val name: String) extends IndexVariable {
  override def sort: Sort = throw new IllegalStateException("placeholder variable has no sort")

  def withSort(sort: Sort): IVBound = new IVBound(name, sort)

  override def toString: String = s"${name}_${super.hashCode.toHexString} : ?"
}

object IVPlaceholder extends Parseable[IVPlaceholder] {
  override def parse(pc: ParseContext): IVPlaceholder =
    val name = pc.pop(Tk.Var).text
    new IVPlaceholder(name)
}
