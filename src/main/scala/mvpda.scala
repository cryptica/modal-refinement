
/**
 * The class AttackRule encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
case class AttackRule[A](lhs: (A, A), rhs: Set[List[A]]) {
  val rhsInternalReturn = rhs filter { _.length <= 2 }
  val rhsInternalCall = rhs filter { _.length >= 2 }

  override def toString =
    lhs.toString + " -> " +(rhs map { _.mkString }).mkString("{",",","}")
}

class LhsAttackSet[A]() {
  val rules = new scala.collection.mutable.HashMap[(A, A),
    List[ ( (A, A), List[A], Set[List[A]] )]]()

  def add(lhs: (A, A), rhsHead: (A, A), rhsTail: List[A], rhsRest: Set[List[A]]): Boolean = {
    rules.get(rhsHead) match {
      case Some(rhslist) =>
        if(rhslist exists { rhs => rhs._1 == lhs && rhs._2 == rhsTail && rhs._3.subsetOf(rhsRest) }) false
        else {
          rules.put(rhsHead, (lhs, rhsTail, rhsRest) :: rhslist)
          true
        }
      case None =>
        rules.put(rhsHead, List((lhs, rhsTail, rhsRest)))
        true
    }
  }
  
  def get(rhsHead: (A, A)) = rules.get(rhsHead) match {
    case Some(rhslist) => rhslist
    case None => Nil
  }
}

class RhsAttackSet[A]() {
  val rules = new scala.collection.mutable.HashMap[(A, A), List[Set[List[A]]]]()

  def add(rule: AttackRule[A]): Boolean = add(rule.lhs, rule.rhs)
  private def add(lhs: (A, A), rhs: Set[List[A]]): Boolean = {
    rules.get(lhs) match {
      case Some(rhslist) =>
        if(rhslist exists { _.subsetOf(rhs) }) false
        else {
          rules.put(lhs, rhs :: rhslist)
          true
        }
      case None =>
        rules.put(lhs, List(rhs))
        true
    }
  }

  def get(lhs: (A, A)) = rules.get(lhs) match {
    case Some(rhslist) => rhslist
    case None => Nil
  }
}

class MVPDA[A](val initial: (A, A), val rules: Set[AttackRule[A]]) {
  
  override def toString = rules.mkString("\n")

  def applyRules() {
    val lhsRules = new LhsAttackSet[A]()
    val rhsRules = new RhsAttackSet[A]()
    val worklist = new scala.collection.mutable.Queue[AttackRule[A]]()
    worklist ++= rules
    while(worklist.nonEmpty) {
      val rule = worklist.dequeue
      println("Dequeued " + rule)
      var isRhsRule = true
      for{ lhsRhs <- rule.rhs } {
        if(lhsRhs.length >= 2) {
          val lhsRhsHead = (lhsRhs(0), lhsRhs(1))
          val lhsRhsTail = lhsRhs.drop(2)
          if(lhsRules.add(rule.lhs, lhsRhsHead, lhsRhsTail, rule.rhs - lhsRhs)) {
            println("Added to LHS " + rule)
            for{ rhsSet <- rhsRules.get(lhsRhsHead) } {
              val newRhs = (rule.rhs - lhsRhs) | rhsSet
              val newRule = AttackRule(rule.lhs, newRhs)
              println("Created " + newRule)
              worklist += newRule
            }
          }
        }
        if(lhsRhs.length >= 3) {
          isRhsRule = false
        }
      }
      if(isRhsRule) {
        if(rhsRules.add(rule)) {
          println("Added to RHS " + rule)
          for{ (lhs, rhsTail, rhsRest) <- lhsRules.get(rule.lhs) } {
            val newRhs = (rule.rhs map { _ ::: rhsTail }) | rhsRest
            val newRule = AttackRule(lhs, newRhs)
            println("Created " + newRule)
            worklist += newRule
          }
        }
      }
    }
    if(rhsRules.get(initial) exists { _.isEmpty }) {
      println("The states " + initial + " do not refine.\n")
    }
    else {
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
         val rhs2list = for
         { rule2 <- mprs.rules
           lhs2 = rule2.lhs.toList; action2 = rule2.action; rhs2 = rule2.rhs.toList
           type2 = rule1.ruleType
           if lhs2(0) == state2
           if lhs2(1) == symbol2
           if action1 == action2
           if type1 == type2
         } yield rhs2
         val (lhs3, rhs3) = type1 match {
           case MayRule => 
             (((state1, state2), (symbol1, symbol2)),
              (rhs2list map { rhs1 zip _ }).toSet)
           case MustRule => 
             (((state2, state1), (symbol2, symbol1)),
              (rhs2list map { _ zip rhs1 }).toSet)
         }
         AttackRule(lhs3, rhs3)
    }
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val rules = getAttacks(mprs)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    new MVPDA((initial(0), initial(1)), rules)
  }
}
