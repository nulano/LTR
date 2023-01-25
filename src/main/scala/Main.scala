object Main {
  def main(args: Array[String]): Unit = {
    /*
    <<>, inl  { return { fun x . return <> } }   >
    :
    (1) × ((V ^ V (?) -> (^ 1) ) + (?))
    */
    val pc = StringParseContext("<<>, inl  { return { fun x . return <> } }   >")
    val v = Value.parse(pc)
    val s = v.toString
    println(s)
    val v2 = Value.parse(StringParseContext(s))
    println(v equals v2)
    v match {
      case ValPair(left, right) => println(s"pair $left, $right")
      case _ => println("?")
    }
  }
}