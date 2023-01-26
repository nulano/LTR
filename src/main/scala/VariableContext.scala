class VariableContext(val vars: List[(String, PType)]) {

  // TODO check for name conflicts
  def add(name: String, tp: PType): VariableContext = VariableContext((name, tp) :: vars)
  
  def find(name: String): Option[PType] = vars.find(_._1 == name).map(_._2)

  def check(name: String, tp: PType): Boolean = find(name).contains(tp)

}
