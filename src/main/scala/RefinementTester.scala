import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.PriorityQueue

/**
 * This class tests refinement for a given mvPDA.
 */
class RefinementTester[A](mvPDA: MVPDA[A]) {

  // the working list contains rules not yet processed
  private val workingList = new PriorityQueue[AttackRule[A]]()(Ordering.by{ rule => -(rule.size) })
  // the state set contains all states visited so far
  private val stateSet = new HashSet[InternalState[A]]()

  // contains all constructed attack rules, with the key from the lhs
  private val allMap = new HashMap[InternalState[A], Set[AttackRule[A]]]()
  // contains all constructed right-hand side attack rules, with the key from the lhs
  private val rhsMap = new HashMap[InternalState[A], Set[RhsAttackRule[A]]]()
  // contains all constructed left-hand side attack rules, with a key from each rhs
  private val lhsMap = new HashMap[InternalState[A], Set[LhsAttackRule[A]]]()
  
  /**
   * Add the given state and create attacks rules for it
   * if it was not visited before.
   */
  private def addState(lhs: InternalState[A]) {
    if(stateSet.add(lhs)) {
      addAttacksFrom(lhs)
    }
  }

  /**
   * Try to add an attack rule to the set of rules.
   * Returns true the rule was added, otherwise false.
   */
  private def addRule(rule: AttackRule[A]): Boolean = {
    var rules = allMap.getOrElse(rule.lhs, Set.empty)
    if(rules.contains(rule)) {
      // rule already added
      return false
    }
    // check for inclusion of rules
    rules foreach { oldRule =>
      if(oldRule <= rule) {
        // a smaller rule already exists, therefore the rule is not needed
        return false
      }
      if(rule <= oldRule) {
        // a bigger rule exists, remove it
        rules -= oldRule
        oldRule match {
          case lhsRule @ LhsAttackRule(_,_,rhsInternal,_,rhsCallMap) => 
            (rhsInternal | rhsCallMap.keySet) foreach { rhs =>
              lhsMap += ((rhs, lhsMap(rhs) - lhsRule))
            }
          case rhsRule @ RhsAttackRule(lhs,_) => 
            rhsMap += ((lhs, rhsMap(lhs) - rhsRule))
        }
      }
    }
    // add rule to each map
    allMap += ((rule.lhs, rules + rule))
    rule match {
      case lhsRule @ LhsAttackRule(_,_,rhsInternal,_,rhsCallMap) => 
        (rhsInternal | rhsCallMap.keySet) foreach { rhs =>
          lhsMap += ((rhs, lhsMap.getOrElse(rhs, Set.empty) + lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap.getOrElse(lhs, Set.empty) + rhsRule))
    }
    return true
  }

  /**
   * Add a rule to the worklist if it
   * was not already added to the set of rules.
   */
  private def addToWorklist(rule: AttackRule[A]) {
    val rules = allMap.getOrElse(rule.lhs, Set.empty)
    if(!(rules exists { _ <= rule })) {
      workingList += rule
    }
  }
  
  /**
   * Add all the basic attack rules that are possible from the
   * given lhs to the worklist.
   */ 
  private def addAttacksFrom(lhs: InternalState[A]) {
    // construct a rule from the map for rewrite rules of a certain type
    // given a function to make a state and an attack rule
    def makeRuleFrom[B, C](
      rulesMap: Map[(String, RuleType), Map[Internal[A], Set[B]]]
    )(makeState: (B, B) => C)(makeRule: Set[C] => AttackRule[A]) = {
      for {
        ((_, ruleType), rhsMap) <- rulesMap
        (lhs1, lhs2) = ruleType match {
          case MayRule => (lhs.left, lhs.right)
          case MustRule => (lhs.right, lhs.left)
        }
        rhs1 <- rhsMap.getOrElse(lhs1, Set.empty)
      } {
        val rhs = rhsMap.getOrElse(lhs2, Set.empty) map {
          rhs2 => ruleType match {
            case MayRule => makeState(rhs1, rhs2)
            case MustRule => makeState(rhs2, rhs1)
          }
        }
        addToWorklist(makeRule(rhs))
      }
    }
    // make rules from each type of rule
    makeRuleFrom(mvPDA.returnRules)
      { (r1, r2) => ReturnState(r1, r2) }
      { AttackRule.makeReturnRule(lhs, _) }
    makeRuleFrom(mvPDA.internalRules)
      { (r1, r2) => InternalState(r1, r2) }
      { AttackRule.makeInternalRule(lhs, _) }
    makeRuleFrom(mvPDA.callRules)
      { (r1, r2) => CallState(r1, r2) }
      { AttackRule.makeCallRule(lhs, _) }
  }

  /**
   * Add all the combined attack rules that can be created by
   * the given left-hand side and right-hand side rule 
   * to the worklist.
   */ 
  private def combine(lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]) {
    // matching on internal states
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      // remove internal state and add return states
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = AttackRule.makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal,
          lhsRule.rhsCall, lhsRule.rhsCallMap)
      addToWorklist(rule)
    }
    // matching on call states
    lhsRule.rhsCallMap.get(rhsRule.lhs) foreach { callTails =>
      callTails foreach { callTail =>
        // remove head and combine return with tail for new internal state
        val newCallTails = callTails - callTail
        val newRhsCallMap = if(newCallTails.isEmpty) {
            lhsRule.rhsCallMap - rhsRule.lhs
          }
          else {
            lhsRule.rhsCallMap + ((rhsRule.lhs, newCallTails))
          }
        val newRhsInternal =
          lhsRule.rhsInternal | (rhsRule.rhsReturn map { rhs => rhs + callTail })
        val newRhsCall = lhsRule.rhsCall - (rhsRule.lhs + callTail)
        val rule = AttackRule.makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal,
            newRhsCall, newRhsCallMap)
        addToWorklist(rule)
      }
    }
  }
  
  /**
   * Test refinement on the given pair of processes.
   * Returns true if refinement holds, otherwise fals.
   * If verbose is set to true each rule is printed to
   * the standard output.
   */
  def testRefinement(initial: InternalState[A], verbose: Boolean = false): Boolean = {
    addState(initial)
    var counter = 0
    while(workingList.nonEmpty) {
      // get rule from worklist
      val rule = workingList.dequeue
      if(verbose) {
        println(counter + ": " + rule)
      }
      if(rule.lhs == initial && rule.size == 0) {
        // winning strategy for the attacker has been found
        return false
      }
      else if(addRule(rule)) {
        counter += 1
        rule match {
          case lhsRule @ LhsAttackRule(_,_,rhsInternal,_,rhsCallMap) =>
            (rhsInternal | rhsCallMap.keySet) foreach { lhsRhs =>
              // possibly add new state
              addState(lhsRhs)
              // combine with every matching right-hand side rule
              rhsMap.getOrElse(lhsRhs, Set.empty) foreach { rhsRule =>
                combine(lhsRule, rhsRule)
              }
            }
          case rhsRule @ RhsAttackRule(lhs,_) =>
            // combine with every matching left-hand side rule
            lhsMap.getOrElse(lhs, Set.empty) foreach { lhsRule =>
              combine(lhsRule, rhsRule)
            }
        }
      }
    }
    // no winning strategy for the attacker has been found
    return true
  }
}
