
trait IndexVariable {
  def name: String
  def sort: Sort
}

class IVSimple(val name: String, val sort: Sort) extends IndexVariable {
  override def toString: String = s"${name}_${super.hashCode.toHexString} : $sort"
}

object IVSimple extends Parseable[IndexVariable] {
  override def parse(pc: ParseContext): IVSimple =
    val name = pc.pop(Tk.Var).text
    pc.pop(Tk.Colon)
    val sort = Sort.parse(pc)
    new IVSimple(name, sort)
}

class IVPlaceholder(val name: String) extends IndexVariable {
  override def sort: Sort = throw new IllegalStateException("placeholder variable has no sort")

  def withSort(sort: Sort): IVSimple = new IVSimple(name, sort)

  override def toString: String = s"${name}_${super.hashCode.toHexString} : ?"
}

object IVPlaceholder extends Parseable[IVPlaceholder] {
  override def parse(pc: ParseContext): IVPlaceholder =
    val name = pc.pop(Tk.Var).text
    new IVPlaceholder(name)
}
