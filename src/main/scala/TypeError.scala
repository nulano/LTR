
class TypeException(msg: String) extends Exception(msg)

object TypeException {
  def apply(msg: String): TypeException = new TypeException(msg)
}

case class SortException(index: Index, msg: String) extends TypeException(s"$msg in '$index'")

