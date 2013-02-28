
/*
case class AttackRule(lhs: Process, action: String, rhs: Set[Process]) {
  val states = lhs.head.constants | (rhs flatMap {_.head.constants })
  val symbols = lhs.tail.constants | (rhs flatMap {_.tail.constants })
}
*/
case class AttackRule[A](
  val lhs: List[A],
  val action: List[(String, Int)],
  val rhs: Set[List[A]]) {

  override def toString =
    lhs.mkString + action.mkString(" -","","-> ") +
    (rhs map { _.mkString }).mkString("{",",","}")

  private def replace(term: List[A], in: List[A]): Option[Set[List[A]]] =
  (term, in) match {
    case (Nil, y :: ys) => Some(rhs map { _ ::: in })
    case (x :: xs, y :: ys) if x == y => replace(xs, ys)
    case _ => None
  }
  def apply(on: List[A]): Option[Set[List[A]]] = {
    replace(lhs, on)
  }
}

class AttackSet[A]() extends Iterable[AttackRule[A]] {
  val rules = new scala.collection.mutable.HashMap[List[A], List[(List[(String, Int)], Set[List[A]])]]()

  def add(rule: AttackRule[A]): Boolean = add(rule.lhs, rule.action, rule.rhs)
  def add(lhs: List[A], action: List[(String, Int)], rhs: Set[List[A]]): Boolean = {
    rules.get(lhs) match {
      case Some(arhslist) =>
        if(arhslist exists { _._2.subsetOf(rhs) }) false
        else {
          rules.put(lhs, (action, rhs) :: arhslist)
          true
        }
      case None =>
        rules.put(lhs, List((action, rhs)))
        true
    }
  }

  def iterator = new AttackSetIterator()

  class AttackSetIterator() extends Iterator[AttackRule[A]] {
    val ruleIterator = rules.iterator
    var rule: Option[(List[A], Iterator[(List[(String, Int)], Set[List[A]])])] = None
    
    private def advance() {
      val kv = ruleIterator.next
      val lhs = kv._1
      val arhslist = kv._2
      rule = Some((lhs, arhslist.iterator))
    }
    def next: AttackRule[A] = rule match {
      case Some((lhs, it)) if it.hasNext =>
        val arhs = it.next
        val action = arhs._1
        val rhs = arhs._2
        AttackRule(lhs, action, rhs)
      case _ =>
        advance()
        next
    }
    def hasNext: Boolean = rule match {
      case Some((_, it)) if it.hasNext => true
      case _ => ruleIterator.hasNext
    }
  }
}

class MVPDA[A](val initial: List[A], val rules: Set[AttackRule[A]]) {
  
  override def toString = rules.mkString("\n")

  def applyRules() {
    val lhsRules = new AttackSet[A]()
    val rhsRules = new AttackSet[A]()
    def addRule(rule: AttackRule[A]): Boolean = {
      var added = false
      if(rule.rhs forall { _.length < 3 }) {
        if(rhsRules.add(rule)) added = true
      }
      if(rule.rhs exists { _.length > 2 }) {
        if(lhsRules.add(rule)) added = true
      }
      added
    }
    rules foreach { addRule(_) }
    var morerules = true
    while(morerules) {
      morerules = false
      for{lhsRule <- lhsRules
         rhsRule <- rhsRules
         lhsRhs <- lhsRule.rhs
         if lhsRhs.length < 3 || (rhsRule.rhs forall { _.length < 3 })
      } {
        rhsRule.apply(lhsRhs) match {
          case Some(matchSet) =>
            val newset = (lhsRule.rhs - lhsRhs) | matchSet
            val newrule = AttackRule(lhsRule.lhs, lhsRule.action ::: rhsRule.action, newset)
            if(addRule(newrule)) {
              println("Added " + newrule)
              morerules = true
            }
          case None =>
        }
      }
    }
    println("Final set of lhs rules: ")
    println(lhsRules.mkString("\n"))
    println("Final set of rhs rules: ")
    println(rhsRules.mkString("\n"))
    println("States that don't refine: ")
    for{ rule <- rhsRules } {
      if(rule.rhs.isEmpty) {
        println(rule)
      }
    }
    (rhsRules find { rule => rule.lhs == initial && rule.rhs.isEmpty }) match {
      case Some(rule) =>
        println("The states " + initial + " do not refine.\n" +
                "Attackers winning strategy: " + rule.action.mkString)
      case None =>
        println("The states " + initial + " do refine.")
    }
  }
}

object MVPDA {

  def getAttacks[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val states = mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }
    val symbols = mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.rhs.tail.constants }
    for
      {state1 <- states
       state2 <- states
       symbol1 <- symbols
       symbol2 <- symbols
       rule1 <- mprs.rules
       lhs1 = rule1.lhs.toList; action1 = rule1.action; rhs1 = rule1.rhs.toList
       type1 = rule1.ruleType
       if lhs1(0) == state1
       if lhs1(1) == symbol1
      } yield {
         val rhs2list = for
         { rule2 <- mprs.rules
           lhs2 = rule2.lhs.toList; action2 = rule2.action; rhs2 = rule2.rhs.toList
           type2 = rule1.ruleType
           if lhs2(0) == state2
           if lhs2(1) == symbol2
           if action1 == action2
           if type1 == type2
         } yield rhs2
         type1 match {
           case MayRule => 
             val lhs3 = List((state1, state2), (symbol1, symbol2))
             val rhs3 = rhs2list map { rhs1 zip _ }
             AttackRule(lhs3, List((action1, 0)), rhs3.toSet)
           case MustRule => 
             val lhs3 = List((state2, state1), (symbol2, symbol1))
             val rhs3 = rhs2list map { _ zip rhs1 }
             AttackRule(lhs3, List((action1, 1)), rhs3.toSet)
         }
    }
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val rules = getAttacks(mprs)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    new MVPDA(initial, rules)
  }
}
