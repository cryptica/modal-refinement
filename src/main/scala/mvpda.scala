import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.TreeSet
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.PriorityQueue
import scala.collection.mutable.Queue

/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
abstract sealed class AttackRule[A] {
  val lhs: (A, A)
  val rhs: Set[List[A]]
  override def toString =
    lhs.toString + " -> " + (rhs map { _.mkString }).mkString("{",",","}")
}
case class LhsAttackRule[A](lhs: (A, A), rhsInternal: Set[(A, A)], rhsCall: Map[(A, A), Set[A]], rhsReturn: Set[A]) extends AttackRule[A] {
  override val hashCode = 41*(41*(41*(41 + lhs.hashCode) + rhsInternal.hashCode) + rhsCall.hashCode) + rhsReturn.hashCode
  val rhs =
    (rhsReturn map { rhs => List(rhs) }) |
    (rhsInternal map { rhs => List(rhs._1, rhs._2) }) |
    (rhsCall flatMap { rhs => rhs._2 map { List(rhs._1._1, rhs._1._2, _) } }).toSet
}
case class RhsAttackRule[A](lhs: (A, A), rhsReturn: Set[A]) extends AttackRule[A] {
  override val hashCode = 31*(31 + lhs.hashCode) + rhsReturn.hashCode
  val rhs = (rhsReturn map { rhs => List(rhs) })
}
object AttackRule {
  private def partition[A](rhs: Set[List[A]]) = {
    val groups = rhs groupBy { _.size  }
    val rhsReturnFull = groups.getOrElse(1, Set.empty)
    val rhsInternalFull = groups.getOrElse(2, Set.empty)
    val rhsCallFull = groups.getOrElse(3, Set.empty)
    val rhsReturn = (rhsReturnFull map { _(0) })
    val rhsInternal = (rhsInternalFull map { rhs => (rhs(0), rhs(1)) })
    var rhsCall = Map[(A, A), Set[A]]()
    rhsCallFull foreach { rhs =>
      val head = (rhs(0), rhs(1))
      val tail = rhs(2)
      val entry = rhsCall.getOrElse(head, Set.empty) + tail
      rhsCall += ((head, entry))
    }
    (rhsReturn, rhsInternal, rhsCall)
  }

  def makeRule[A](lhs: (A, A), rhsReturn: Set[A], rhsInternal: Set[(A, A)], rhsCall: Map[(A, A), Set[A]]): AttackRule[A] = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule(lhs, rhsReturn)
    }
    else {
      LhsAttackRule(lhs, rhsInternal, rhsCall, rhsReturn)
    }
  }

  def makeRule[A](lhs: (A, A), rhs: Set[List[A]]): AttackRule[A] = {
    val (rhsReturn, rhsInternal, rhsCall) = partition(rhs)
    makeRule(lhs, rhsReturn, rhsInternal, rhsCall)
  }
}

class RuleOrdering[A] extends Ordering[AttackRule[A]] {
  override def compare(x: AttackRule[A], y: AttackRule[A]) = {
    y.rhs.size compare x.rhs.size
  }
}

class RefinementTester[B](mprs: MPRS[B]) {
  type A = (B, B)

  val workingSet = new PriorityQueue[AttackRule[A]]()(new RuleOrdering())
  val stateSet = new HashSet[(A, A)]()

  val allMap = new HashMap[(A, A), Set[AttackRule[A]]]()
  val rhsMap = new HashMap[(A, A), Set[RhsAttackRule[A]]]()
  val lhsMap = new HashMap[(A, A), Set[LhsAttackRule[A]]]()
  var numRules = 0
  
  val arities = new HashMap[String, Int]()
  def isVPDA[B](mprs: MPRS[B]) = {
    mprs.rules forall { rule => 
      val (action, arity) = rule match {
        case RewriteRule(_, _ +: Const(_), a, Const(_)) => (a, 1)
        case RewriteRule(_, _ +: Const(_), a, _ +: Const(_)) => (a, 2)
        case RewriteRule(_, _ +: Const(_), a, _ +: _ +: Const(_)) => (a, 3)
        case _ => ("", -1)
      }
      arity >= 0 && (arities.put(action, arity) forall { _ == arity })
    }
  }

  def addRulesFrom(lhs: (A, A)) {
    if(stateSet.add(lhs)) {
      println("New lhs " + lhs)
      addAttacksFrom(lhs)
    }
  }

  def remove(rule: AttackRule[A]) {
    //workingSet -= rule
    allMap += ((rule.lhs, allMap(rule.lhs) - rule))
    numRules -= 1
    rule match {
      case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) => 
        (rhsInternal | rhsCall.keySet) foreach { rhs =>
          lhsMap += ((rhs, lhsMap(rhs) - lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap(lhs) - rhsRule))
    }
  }

  def ruleIncluded(oldRule: AttackRule[A], newRule: AttackRule[A]) = {
    oldRule.lhs == newRule.lhs &&
    oldRule.rhs.subsetOf(newRule.rhs)
  }

  private def addNew(rule: AttackRule[A]) {
    workingSet += rule
    allMap += ((rule.lhs, allMap.getOrElse(rule.lhs, Set.empty) + rule))
    numRules += 1
    rule match {
      case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) => 
        (rhsInternal | rhsCall.keySet) foreach { rhs =>
          lhsMap += ((rhs, lhsMap.getOrElse(rhs, Set.empty) + lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap.getOrElse(lhs, Set.empty) + rhsRule))
    }
  }

  def add(rule: AttackRule[A]) {
    val rules = allMap.getOrElse(rule.lhs, Set.empty)
    if(!(rules exists { ruleIncluded(_, rule) })) {
      rules foreach { oldRule =>
        if(ruleIncluded(rule, oldRule)) {
          remove(oldRule)
        }
      }
      addNew(rule)
    }
  }
  
  /**
   * Get all the attacks that are possible from a state under
   * the given mPRS.
   * @param lhs the paired state from which the attack is done
   * @param mprs the original mPRS with the transition rules
   * @return a list of AttackRules starting from the given state
   */ 
  def addAttacksFrom(lhs: ((B, B), (B, B))) {
    val lhs1 = List(lhs._1._1, lhs._2._1)
    val lhs2 = List(lhs._1._2, lhs._2._2)
    for {
       // iterate over all attacking rules
       rule1 <- mprs.rules
       rule1lhs = rule1.lhs.toList
       // attack from left for may rule and from right for must rule
       if (rule1.ruleType == MayRule && lhs1 == rule1lhs) ||
          (rule1.ruleType == MustRule && lhs2 == rule1lhs)
       rhs1 = rule1.rhs.toList
    } yield {
      val rhs2list = for {
        // iterate over all defending rules fitting the attack rule
        rule2 <- mprs.rules
        rule2lhs = rule2.lhs.toList
        if rule1.ruleType == rule2.ruleType
        if rule1.action == rule2.action
       // defend from right for may rule and from left for must rule
        if (rule2.ruleType == MayRule && lhs2 == rule2lhs) ||
           (rule2.ruleType == MustRule && lhs1 == rule2lhs)
      } yield rule2.rhs.toList
      // create the new right-hand side
      val rhs3 = rule1.ruleType match {
        case MayRule => (rhs2list map { rhs1 zip _ })
        case MustRule => (rhs2list map { _ zip rhs1 })
      }
      val rule = AttackRule.makeRule(lhs, rhs3)
      println("Created rule " + rule + " from " + rule1)
      add(rule)
    }
  }

  def combine(lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]) {
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = AttackRule.makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal, lhsRule.rhsCall)
      println("Combined rule " + rule)
      add(rule)
    }
    lhsRule.rhsCall.get(rhsRule.lhs) foreach { callTails =>
      callTails foreach { callTail =>
        val newCallTails = callTails - callTail
        val newRhsCall = if(newCallTails.isEmpty) {
            lhsRule.rhsCall - rhsRule.lhs
          }
          else {
            lhsRule.rhsCall + ((rhsRule.lhs, newCallTails))
          }
        val newRhsInternal = lhsRule.rhsInternal |
            (rhsRule.rhsReturn map { (_, callTail) })
        val rule = AttackRule.makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal, newRhsCall)
        println("Combined rule " + rule)
        add(rule)
      }
    }
  }
  
  /**
   * On the given mPRS, which needs to be a vPDA, test if
   * the lhs initial state refines the rhs initial state and return
   * the result.
   * @param the modal process rewrite system to tested for refinement.
   *        the system needs to be a visible PDA
   * @return true if the lhs state of the mPRS refines the rhs state,
   *         otherwise false
   */
  def testRefinement(): Boolean = {
    if(!isVPDA(mprs)) {
      throw new IllegalArgumentException("Given mPRS is not a vPDA")
    }
    // encode all states as pairs (lhs, rhs)
    val initialList = mprs.initialLHS.toList zip mprs.initialRHS.toList
    val initial = (initialList(0), initialList(1))
    // initialize rules with rules from initial state
    addRulesFrom(initial)
    var counter = 0
    var obsolete = 0
    while(workingSet.nonEmpty) {
      // get rule from worklist
      counter += 1
      val rule = workingSet.dequeue
      if((counter < 50) || (counter < 100 && counter % 10 == 0) || (counter < 1000 && counter % 100 == 0) || counter % 1000 == 0) {
        //println("Got from worklist rule num " + counter)
        //println("Num of all rules: " + ((0, 0) /: allMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Num of rhs rules: " + ((0, 0) /: rhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Num of lhs rules: " + ((0, 0) /: lhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Number of obsolete rules is " + obsolete)
        println("Cur rule is " + rule)
      }
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.rhs.isEmpty) {
        println("Found winning strategy " + rule)
        return false
      }
      else if(allMap(rule.lhs) exists { oldRule =>
        ruleIncluded(oldRule, rule) && !ruleIncluded(rule, oldRule) } ) {
        obsolete += 1
      }
      else {
        rule match {
          case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) =>
            for{ lhsRhs <- (rhsInternal | rhsCall.keySet) } {
              addRulesFrom(lhsRhs)
              for{ rhsRule <- rhsMap.getOrElse(lhsRhs, Set.empty) } {
                combine(lhsRule, rhsRule)
              }
            }
          case rhsRule @ RhsAttackRule(lhs,_) =>
            for{ lhsRule <- lhsMap.getOrElse(lhs, Set.empty) } {
              combine(lhsRule, rhsRule)
            }
        }
      }
    }
    // no winning strategy for attacker found, so the states refine
    println("Total number of rules is " + numRules)
    println("Number of obsolete rules is " + obsolete)
    return true
  }
}

object MVPDA {
  
  def testRefinement[B](mprs: MPRS[B]): Boolean = {
    val tester = new RefinementTester(mprs)
    tester.testRefinement()
  }

  /**
   * On the given mPRS, which needs to be a vPDA, test if
   * the lhs initial state refines the rhs initial state and return
   * the result.
   * @param the modal process rewrite system to tested for refinement.
   *        the system needs to be a visible PDA
   * @return true if the lhs state of the mPRS refines the rhs state,
   *         otherwise false
   */
  
  /**
   * Test if the given modal process rewrite system is
   * a visible PDA. An mPRS is a vPDA if the actions can
   * be partitioned into three sets for internal, call or
   * return actions.
   * @param mprs the mPRS to be tested
   * @return true if the mPRS is a vPDA, otherwise false
   */ 
  def isVPDA[B](mprs: MPRS[B]) = {
    val arities = new HashMap[String, Int]()
    mprs.rules forall { rule => 
      val (action, arity) = rule match {
        case RewriteRule(_, _ +: Const(_), a, Const(_)) => (a, 0)
        case RewriteRule(_, _ +: Const(_), a, _ +: Const(_)) => (a, 1)
        case RewriteRule(_, _ +: Const(_), a, _ +: _ +: Const(_)) => (a, 2)
        case _ => ("", -1)
      }
      arity >= 0 && (arities.put(action, arity) forall { _ == arity })
    }
  }
}
