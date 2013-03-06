
/**
 * The class AttackRule encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
case class AttackRule[A](lhs: List[A], rhs: Set[List[A]]) {
  override def toString =
    lhs.mkString + " -> " +(rhs map { _.mkString }).mkString("{",",","}")
}

abstract class AttackSet[A] {
  type Elem
  val rules = new scala.collection.mutable.HashMap[List[A], List[Elem]]()
  
  def elemEqual(oldElem: Elem, newElem: Elem): Boolean

  def add(key: List[A], elem: Elem): Boolean = {
    rules.get(key) match {
      case Some(elemlist) =>
        if(elemlist exists { elemEqual(_, elem) }) false
        else {
          rules.put(key, elem :: elemlist)
          true
        }
      case None =>
        rules.put(key, List(elem))
        true
    }
  }
  
  def get(key: List[A]) = rules.get(key) match {
    case Some(elemlist) => elemlist
    case None => Nil
  }
}

class LhsAttackSet[A] extends AttackSet[A] {
  type Elem = ( List[A], List[A], Set[List[A]] )
  
  override def elemEqual(oldElem: Elem, newElem: Elem) = {
    oldElem._1 == newElem._1 &&
    oldElem._2 == newElem._2 &&
    oldElem._3.subsetOf(newElem._3)
  }
}

class RhsAttackSet[A] extends AttackSet[A] {
  type Elem = Set[List[A]]

  override def elemEqual(oldElem: Elem, newElem: Elem) = {
    oldElem.subsetOf(newElem)
  }
}

class MVPDA[A](val initial: List[A], val rules: Set[AttackRule[A]]) {
  
  override def toString = rules.mkString("\n")

  def applyRules() {
    val lhsRules = new LhsAttackSet[A]()
    val rhsRules = new RhsAttackSet[A]()
    val worklist = new scala.collection.mutable.Queue[AttackRule[A]]()
    worklist ++= rules
    var refine = true
    while(worklist.nonEmpty && refine) {
      val rule = worklist.dequeue
      println("Dequeued " + rule)
      if(rule.lhs == initial && rule.rhs.isEmpty) {
        refine == false
      }
      else {
        var isRhsRule = true
        for{ lhsRhs <- rule.rhs } {
          if(lhsRhs.length >= 2) {
            val lhsRhsHead = lhsRhs.take(2)//(lhsRhs(0), lhsRhs(1))
            val lhsRhsTail = lhsRhs.drop(2)
            if(lhsRules.add(lhsRhsHead, (rule.lhs, lhsRhsTail, rule.rhs - lhsRhs))) {
              println("Added to LHS " + rule)
              for{ rhsSet <- rhsRules.get(lhsRhsHead) } {
                val newRhs = (rule.rhs - lhsRhs) | rhsSet
                val newRule = AttackRule(rule.lhs, newRhs)
                println("Created from LHS " + newRule)
                worklist += newRule
              }
            }
          }
          if(lhsRhs.length >= 3) {
            isRhsRule = false
          }
        }
        if(isRhsRule) {
          if(rhsRules.add(rule.lhs, rule.rhs)) {
            println("Added to RHS " + rule)
            for{ (lhs, rhsTail, rhsRest) <- lhsRules.get(rule.lhs) } {
              val newRhs = (rule.rhs map { _ ::: rhsTail }) | rhsRest
              val newRule = AttackRule(lhs, newRhs)
              println("Created from RHS " + newRule)
              worklist += newRule
            }
          }
        }
      }
    }
    if(refine) {
      println("The states " + initial + " do not refine.\n")
    }
    else {
      println("The states " + initial + " do refine.")
    }
  }
}

object MVPDA {

  def getAttacks[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val states = (mprs.rules flatMap { rule => rule.lhs.head.constants | rule.rhs.head.constants }) | mprs.initialLHS.head.constants | mprs.initialRHS.head.constants
    val symbols = (mprs.rules flatMap { rule => rule.lhs.tail.constants | rule.rhs.tail.constants }) | mprs.initialLHS.tail.constants | mprs.initialRHS.tail.constants
    println("States: " + states)
    println("Symbols: " + symbols)
    for
      {state1 <- states
       state2 <- states
       symbol1 <- symbols
       symbol2 <- symbols
       plhs1 = List(state1, symbol1)
       plhs2 = List(state2, symbol2)
       rule1 <- mprs.rules
       lhs1 = rule1.lhs.toList; action1 = rule1.action; rhs1 = rule1.rhs.toList
       type1 = rule1.ruleType
       if lhs1 == plhs1
      } yield {
         val rhs2list = for
         { rule2 <- mprs.rules
           lhs2 = rule2.lhs.toList; action2 = rule2.action; rhs2 = rule2.rhs.toList
           type2 = rule1.ruleType
           if lhs2 == plhs2
           if type1 == type2
         } yield rhs2
         val (lhs3, rhs3) = type1 match {
           case MayRule => 
             (plhs1 zip plhs2, (rhs2list map { rhs1 zip _ }).toSet)
           case MustRule => 
             (plhs2 zip plhs1, (rhs2list map { _ zip rhs1 }).toSet)
         }
         AttackRule(lhs3, rhs3)
    }
  }

  def fromMPRS[A](mprs: MPRS[A])(implicit ordA: Ordering[A]) = {
    val rules = getAttacks(mprs)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    new MVPDA(initial, rules)
  }
}
