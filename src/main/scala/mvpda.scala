
case class StrategyTree[A](rule: RewriteRule[A], children: List[StrategyTree[A]])

/**
 * The class AttackRule encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param action the origin state
 * @param rhs the set of possible destination states
 */
case class AttackRule[A](
  val lhs: (A, A),
  val action: StrategyTree[A],
  val rhs: Set[List[A]]) {

  override def toString =
    lhs.toString + action.toString +
    (rhs map { _.mkString }).mkString("{",",","}")

  /**
   * Apply this rule on a target state. If the rule matches,
   * return the set of new possible resulting states.
   * @param target 
   * @return an option which is None if the rule does not match and
   *         Some containing a set of resulting staes if it does match
   */
  def apply(target: List[A]): Option[Set[List[A]]] = (lhs, target) match {
    case ((x1, x2), y1 :: y2 :: ys) if x1 == y1 && x2 == y2 =>
      Some(rhs map { _ ::: ys })
    case _ => None
  }
}

class AttackSet[A]() extends Iterable[AttackRule[A]] {
  val rules = new scala.collection.mutable.HashMap[(A, A), List[(StrategyTree[A], Set[List[A]])]]()

  def add(rule: AttackRule[A]): Boolean = add(rule.lhs, rule.action, rule.rhs)
  private def add(lhs: (A, A), action: StrategyTree[A], rhs: Set[List[A]]): Boolean = {
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

  def get(lhs: (A, A)) = 
    rules.get(lhs) match {
      case Some(arhslist) => arhslist
      case None => Nil
    }

  def remove(rule: AttackRule[A]): Boolean = {
    rules.get(rule.lhs) match {
      case Some(arhslist) =>
        if(arhslist exists { _._2.subsetOf(rule.rhs) }) {
          //TODO
          true
        }
        else false
      case None => false
    }
  }
  def contains(rule: AttackRule[A]): Boolean = {
    rules.get(rule.lhs) match {
      case Some(arhslist) =>
        if(arhslist exists { _._2.subsetOf(rule.rhs) }) true
        else false
      case None => false
    }
  }

  def iterator = new AttackSetIterator()

  class AttackSetIterator() extends Iterator[AttackRule[A]] {
    val ruleIterator = rules.iterator
    var rule: Option[((A, A), Iterator[(StrategyTree[A], Set[List[A]])])] = None
    
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

class MVPDA[A](val initial: (A, A), val rules: Set[AttackRule[A]]) {
  
  override def toString = rules.mkString("\n")

  def applyRules() {
    val lhsRules = new AttackSet[A]()
    val rhsRules = new AttackSet[A]()
    def addRule(rule: AttackRule[A]): Boolean = {
      var added = false
      if(rule.rhs exists { _.length >= 2 }) {
        if(lhsRules.add(rule)) added = true
      }
      if(rule.rhs forall { _.length <= 2 }) {
        if(rhsRules.add(rule)) added = true
      }
      added
    }
    rules foreach { addRule(_) }
    var morerules = true
    while(morerules) {
      morerules = false
      for{lhsRule <- lhsRules
         lhsRhs <- lhsRule.rhs
         rhsRuleList = rhsRules.get((lhsRhs(0), lhsRhs(1)))
         (strategySet, rhsSet) <- rhsRuleList
      } {
        val newRhs = (lhsRule.rhs - lhsRhs) | rhsSet
        val newStrategy = StrategyTree(lhsRule.action.rule, List(strategySet)) //TODO
        val newRule = AttackRule(lhsRule.lhs, newStrategy, newRhs)
        if(addRule(newRule)) {
          println("Added " + newRule)
          morerules = true
        }
      }
    }
    /*println("Final set of lhs rules: ")
    println(lhsRules.mkString("\n"))
    println("Final set of rhs rules: ")
    println(rhsRules.mkString("\n"))
    println("States that don't refine: ")
    for{ rule <- rhsRules } {
      if(rule.rhs.isEmpty) {
        println(rule)
      }
    }*/
    (rhsRules find { rule => rule.lhs == initial && rule.rhs.isEmpty }) match {
      case Some(rule) =>
        println("The states " + initial + " do not refine.\n" +
          "Attackers winning strategy: " + rule.action.toString)
      case None =>
        println("The states " + initial + " do refine.")
    }
  }
}

object MVPDA {

  def getAttacks[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val states = mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }
    val symbols = mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.rhs.tail.constants }
    println("States: " + states)
    println("Symbols: " + symbols)
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
         val rhs2rulelist = for
         { rule2 <- mprs.rules
           lhs2 = rule2.lhs.toList; action2 = rule2.action; rhs2 = rule2.rhs.toList
           type2 = rule1.ruleType
           if lhs2(0) == state2
           if lhs2(1) == symbol2
           if action1 == action2
           if type1 == type2
         } yield (rule2, rhs2)
         val rhs2rulelistPair = rhs2rulelist.unzip
         val rules2 = rhs2rulelistPair._1
         val rhs2list = rhs2rulelistPair._2
         type1 match {
           case MayRule => 
             val lhs3 = ((state1, state2), (symbol1, symbol2))
             val rhs3 = (rhs2list map { rhs1 zip _ }).toSet
             val defStrat = rules2 map { AttackRule(_, Nil) }
             AttackRule(lhs3, StrategyTree(rule1, defStrat), rhs3)
           case MustRule => 
             val lhs3 = ((state2, state1), (symbol2, symbol1))
             val rhs3 = (rhs2list map { _ zip rhs1 }).toSet
             val defStrat = rules2 map { AttackRule(_, Nil) }
             AttackRule(lhs3, StrategyTree(rule1, defStrat), rhs3)
         }
    }
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val rules = getAttacks(mprs)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    new MVPDA((initial(0), initial(1)), rules)
  }
}
