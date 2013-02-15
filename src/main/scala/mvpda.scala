
/*
case class AttackRule(lhs: Process, action: String, rhs: Set[Process]) {
  val states = lhs.head.constants | (rhs flatMap {_.head.constants })
  val symbols = lhs.tail.constants | (rhs flatMap {_.tail.constants })
}

class MVPDA(rules: Set[AttackRule]) {
  val actions = rules map { _.action }
  val states = rules map { _.states }
  val symbols = (rules map { _.symbols }).flatten
  
  def print() = {
    for{ rule <- rules; rhs <- rule.rhs } {
      val lhs = rule.lhs
      println(lhs.head + " -> " + rhs.head + " (" + rule.action
        + ";" + lhs.tail + "/" + rhs.tail + ")")
    }
  }
}

object MVPDA {
  def zip[A,B](p: Process[A], q: Process[B])(implicit ordA: Ordering[Process[A]], ordB: Ordering[Process[B]]): Process[(A,B)] = (p, q) match {
    case (Empty, Empty) => Empty
    case (Empty, _) | (Empty, _) => throw new IllegalArgumentException("processes of unequal length")
    case (Const(x), Const(y)) => Const((x, y))
    case (x +: xs, y +: ys) => (x zip y) +: (xs zip ys)
    case (x |: xs, y |: ys) => (x zip y) |: (xs zip ys)
    case _ => throw new IllegalArgumentException("processes of unequal type")
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) {
    val states = mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }
    val symbols = mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.rhs.tail.constants }
    val inital = mprs.initial zip mprs.initial
    new MPRS(inital, rules)
  }
}
*/

object MVPDA {

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val states = mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }
    val symbols = mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.rhs.tail.constants }
    val inital = mprs.initial zip mprs.initial
    val rules = for {rule <- mprs.rules
         symbol <- symbols
         state <- states} yield
       MustRule(
         (rule.lhs.head zip Const(state)) +:
         (rule.lhs.tail zip Const(symbol)),
         rule.toString,
         (rule.rhs.head zip Const(state)) +:
         (rule.rhs.tail zip rule.rhs.tail))
    new MPRS(inital, rules.distinct)
  }
}
