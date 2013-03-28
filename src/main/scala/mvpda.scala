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
abstract sealed class AttackRule[B] {
  val lhs: ((B, B), (B, B))
  val rhs: Set[(List[B], List[B])]
  val size: Int
  override def toString =
    lhs.toString + " -> " + (rhs map { r => "(" + r._1.mkString(".") + "," + r._2.mkString(".") + ")" }).mkString("{",",","}")
}
case class LhsAttackRule[B](lhs: ((B, B), (B, B)), rhsInternal: Set[((B, B), (B, B))], rhsCall: Map[((B, B), (B, B)), Set[(B, B)]], rhsReturn: Set[(B, B)]) extends AttackRule[B] {
  override val hashCode = 41*(41*(41*(41 + lhs.hashCode) + rhsInternal.hashCode) + rhsCall.hashCode) + rhsReturn.hashCode
  val size = rhsInternal.size + rhsCall.size + (rhsCall.values map (_.size)).sum
  val callComplete = (rhsCall flatMap { rhs => rhs._2 map { r => (((rhs._1._1._1, rhs._1._1._2), r._1), ((rhs._1._2._1, rhs._1._2._2), r._2)) } }).toSet
  lazy val rhs = (rhsReturn map { rhs => (List(rhs._1), List(rhs._2)) }) |
    (rhsInternal map { rhs => (List(rhs._1._1, rhs._1._2), List(rhs._2._1, rhs._2._2)) }) |
    (rhsCall flatMap { rhs => rhs._2 map { r => (List(rhs._1._1._1, rhs._1._1._2, r._1), List(rhs._1._2._1, rhs._1._2._2, r._2)) } }).toSet
}
case class RhsAttackRule[B](lhs: ((B, B), (B, B)), rhsReturn: Set[(B, B)]) extends AttackRule[B] {
  override val hashCode = 31*(31 + lhs.hashCode) + rhsReturn.hashCode
  val size = rhsReturn.size
  lazy val rhs = (rhsReturn map { rhs => (List(rhs._1), List(rhs._2)) })
}
object AttackRule {
  private def partition[B](rhs: Set[(List[B], List[B])]) = {
    val groups = rhs groupBy { _._1.size  }
    val rhsReturnFull = groups.getOrElse(1, Set.empty)
    val rhsInternalFull = groups.getOrElse(2, Set.empty)
    val rhsCallFull = groups.getOrElse(3, Set.empty)
    val rhsReturn = (rhsReturnFull map { rhs => (rhs._1(0), rhs._2(0)) })
    val rhsInternal = (rhsInternalFull map { rhs => ((rhs._1(0), rhs._1(1)), (rhs._2(0), rhs._2(1))) })
    var rhsCall = Map[((B, B), (B, B)), Set[(B, B)]]()
    rhsCallFull foreach { rhs =>
      val head = ((rhs._1(0), rhs._1(1)), (rhs._2(0), rhs._2(1)))
      val tail = (rhs._1(2), rhs._2(2))
      val entry = rhsCall.getOrElse(head, Set.empty) + tail
      rhsCall += ((head, entry))
    }
    (rhsReturn, rhsInternal, rhsCall)
  }

  def makeRule[B](lhs: ((B, B), (B, B)), rhsReturn: Set[(B, B)], rhsInternal: Set[((B, B), (B, B))], rhsCall: Map[((B, B), (B, B)), Set[(B, B)]]): AttackRule[B] = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule(lhs, rhsReturn)
    }
    else {
      LhsAttackRule(lhs, rhsInternal, rhsCall, rhsReturn)
    }
  }

  def makeRule[B](lhs: ((B, B), (B, B)), rhs: Set[(List[B], List[B])]): AttackRule[B] = {
    val (rhsReturn, rhsInternal, rhsCall) = partition(rhs)
    makeRule(lhs, rhsReturn, rhsInternal, rhsCall)
  }
}

class RefinementTester[B](mprs: MPRS[B]) {

  val workingSet = new PriorityQueue[AttackRule[B]]()(Ordering.by{ rule => -(rule.size) })
  val stateSet = new HashSet[((B, B), (B, B))]()

  val allMap = new HashMap[((B, B), (B, B)), Set[AttackRule[B]]]()
  val rhsMap = new HashMap[((B, B), (B, B)), Set[RhsAttackRule[B]]]()
  val lhsMap = new HashMap[((B, B), (B, B)), Set[LhsAttackRule[B]]]()
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

  def addRulesFrom(lhs: ((B, B), (B, B))) {
    if(stateSet.add(lhs)) {
      println("New lhs " + lhs)
      addAttacksFrom(lhs)
    }
  }

  def remove(rule: AttackRule[B]) {
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

  def ruleIncluded(oldRule: AttackRule[B], newRule: AttackRule[B]) = {
    oldRule.lhs == newRule.lhs &&
    ((oldRule, newRule) match {
      case (lhs1 @ LhsAttackRule(_,s1,s2,s3), lhs2 @ LhsAttackRule(_,t1,t2,t3)) =>
        s1.subsetOf(t1) && s3.subsetOf(t3) &&
        lhs1.callComplete.subsetOf(lhs2.callComplete)
        //(s2 forall { kv => kv._2.subsetOf(t2.getOrElse(kv._1, Set.empty)) })
      case (RhsAttackRule(_,s3), LhsAttackRule(_,_,_,t3)) =>
        s3.subsetOf(t3)
      case (RhsAttackRule(_,s3), RhsAttackRule(_,t3)) =>
        s3.subsetOf(t3)
      case _ => false
    })
  }

  private def addNew(rule: AttackRule[B]) {
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

  def add(rule: AttackRule[B]) {
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
    val lhs1 = lhs._1//List(lhs._1._1, lhs._2._1)
    val lhs2 = lhs._2//List(lhs._1._2, lhs._2._2)
    for {
       // iterate over all attacking rules
       rule1 <- mprs.rules
       rule1lhs = (rule1.lhs(0), rule1.lhs(1))
       // attack from left for may rule and from right for must rule
       if (rule1.ruleType == MayRule && lhs1 == rule1lhs) ||
          (rule1.ruleType == MustRule && lhs2 == rule1lhs)
       rhs1 = rule1.rhs.toList
    } yield {
      val rhs2list = for {
        // iterate over all defending rules fitting the attack rule
        rule2 <- mprs.rules
        rule2lhs = (rule2.lhs(0), rule2.lhs(1))
        if rule1.ruleType == rule2.ruleType
        if rule1.action == rule2.action
       // defend from right for may rule and from left for must rule
        if (rule2.ruleType == MayRule && lhs2 == rule2lhs) ||
           (rule2.ruleType == MustRule && lhs1 == rule2lhs)
      } yield rule2.rhs.toList
      // create the new right-hand side
      val rhs3 = rule1.ruleType match {
        case MayRule => (rhs2list map { (rhs1, _) })
        case MustRule => (rhs2list map { (_, rhs1) })
      }
      val rule = AttackRule.makeRule(lhs, rhs3)
      //println("Created rule " + rule + " from " + rule1)
      add(rule)
    }
  }

  def combine(lhsRule: LhsAttackRule[B], rhsRule: RhsAttackRule[B]) {
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = AttackRule.makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal, lhsRule.rhsCall)
      //println("Combined rule " + rule + " from " + lhsRule + " and " + rhsRule)
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
          (rhsRule.rhsReturn map { rhs => ((rhs._1, callTail._1), (rhs._2, callTail._2)) })
        val rule = AttackRule.makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal, newRhsCall)
        //println("Combined rule " + rule + " from " + lhsRule + " and " + rhsRule)
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
    val initial = ((mprs.initialLHS(0), mprs.initialLHS(1)), (mprs.initialRHS(0), mprs.initialRHS(1)))
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
        println("Cur rule " + counter + " is " + rule)
      }
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.size == 0) {
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
