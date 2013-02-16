
/*
case class AttackRule(lhs: Process, action: String, rhs: Set[Process]) {
  val states = lhs.head.constants | (rhs flatMap {_.head.constants })
  val symbols = lhs.tail.constants | (rhs flatMap {_.tail.constants })
}
*/
case class AttackRule[A](
  val lhs: Process[A],
  val action: String,
  val rhs: Set[Process[A]]) {

  override def toString = lhs.toString + " " + action + " " + rhs.toString

  def apply(p: Process[A])(implicit ord: Ordering[A]): Set[Process[A]] = {
    RewriteRule.findMatch(lhs, p, rhs)
  }
}

class MVPDA[A](val initial: Process[A], val rules: Seq[AttackRule[A]])(implicit ord: Ordering[A]) {
  
  override def toString = "Initial: " + initial + "\n" + rules.mkString("\n")

  def applyRules() {
    val exrules = scala.collection.mutable.HashSet[AttackRule[A]]()
    exrules ++= rules
    var morerules = true
    while(morerules) {
      morerules = false
      for{rule1 <- exrules
         rule2 <- exrules
         rhs <- rule2.rhs
         if rhs.length < 3 || (rule1.rhs forall { _.length < 3 })
      } {
        val matches = RewriteRule.findMatch(rule1.lhs, rhs, rule1.rhs)
        println("Matches from " + rule1.lhs + "->" + rule1.rhs + " on " + rhs + " are " + matches)
        val newset = (rule2.rhs - rhs) | matches
        val newrule = AttackRule(rule2.lhs, rule1.action, newset)
        if(exrules.add(newrule)) {
          println("Added " + newrule)
          morerules = true
        }
      }
    }
    println(exrules.mkString("\n"))
  }
}

object MVPDA {

  def getAttacks[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val states = mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }
    val symbols = mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.lhs.tail.constants } // only get symbols and states on the left side, symbols and states that just appear on the right side are useless
    val rules = for
      {state1 <- states
       state2 <- states
       symbol1 <- symbols
       symbol2 <- symbols
       rule1 <- mprs.rules
       lhs1 = rule1.lhs; action1 = rule1.action; rhs1 = rule1.rhs
       if lhs1.head == Const(state1)
       if lhs1.tail == Const(symbol1)
     } yield {
         val lhs3 = Const((state1, state2)) +: Const((symbol1, symbol2))
         val rhs3 = for
         { rule2 <- mprs.rules
           lhs2 = rule2.lhs; action2 = rule2.action; rhs2 = rule2.rhs
           if lhs2.head == Const(state2)
           if lhs2.tail == Const(symbol2)
           if action1 == action2
          } yield (rhs1 zip rhs2)
         AttackRule(lhs3, action1, rhs3.toSet)
     }
    rules
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val inital = mprs.initial zip mprs.initial
    val rules = getAttacks(mprs)
    new MVPDA(inital, rules.distinct)
  }
}
