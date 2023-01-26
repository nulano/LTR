object Main {
  def main(args: Array[String]): Unit = {
    /*
    <<>, inl  { return { fun x . return <> } }   >
    :
    (1) × ((V ^ V (?) -> (^ 1) ) + (?))
    */
    val s = "(return <<>, inl  { return { fun x . return < > } }> : ^(1 × (V ^ V (1 ~ ^ 1 ) + 0)  ))"
    val pc = StringParseContext(s)
    val v = BoundExpression.parse(pc)
    val s2 = v.toString
    println(s2)
    val v2 = BoundExpression.parse(StringParseContext(s2))
    println(v equals v2)
    println(v.getType(VariableContext(List())))
  }
}