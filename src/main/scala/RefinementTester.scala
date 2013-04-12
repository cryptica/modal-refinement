import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.PriorityQueue

class RefinementTester[A](mvPDA: MVPDA[A]) {

  val workingList = new PriorityQueue[AttackRule[A]]()(Ordering.by{ rule => -(rule.size) })
  val stateSet = new HashSet[InternalState[A]]()

  val allMap = new HashMap[InternalState[A], Set[AttackRule[A]]]()
  val rhsMap = new HashMap[InternalState[A], Set[RhsAttackRule[A]]]()
  val lhsMap = new HashMap[InternalState[A], Set[LhsAttackRule[A]]]()
  var numRules = 0
  
  private def addRulesFromState(lhs: InternalState[A]) {
    if(stateSet.add(lhs)) {
      addAttacksFrom(lhs)
    }
  }

  private def addRule(rule: AttackRule[A]): Boolean = {
    var rules = allMap.getOrElse(rule.lhs, Set.empty)
    // check for inclusion of rules
    rules foreach { oldRule =>
      // a smaller rule is
      if(oldRule <= rule) {
        return false
      }
      if(rule <= oldRule) {
        rules -= oldRule
        numRules -= 1
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
    // add rule to map
    allMap += ((rule.lhs, rules + rule))
    numRules += 1
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

  def addToWorklist(rule: AttackRule[A]) {
    val rules = allMap.getOrElse(rule.lhs, Set.empty)
    if(!(rules exists { _ <= rule })) {
      workingList += rule
    }
  }
  
  /**
   * Get all the attacks that are possible from a state under
   * the given mPRS.
   * @param lhs the paired state from which the attack is done
   * @param mprs the original mPRS with the transition rules
   * @return a list of AttackRules starting from the given state
   */ 
  def addAttacksFrom(lhs: InternalState[A]) {
    def makeRuleFrom[B, C](
      rulesMap: Map[(String, RuleType), Map[Internal[A], Set[B]]]
    )(makeState: (B, B) => C)(makeRule: Set[C] => AttackRule[A]) = {
      for {
        ((_, ruleType), rhsMap) <- rulesMap
        lhs1 = ruleType match {
          case MayRule => lhs
          case MustRule => lhs.swap
        }
        rhs1 <- rhsMap.getOrElse(lhs1.left, Set.empty)
        rhs2list = rhsMap.getOrElse(lhs1.right, Set.empty)
      } {
        val rhs = rhs2list map { ruleType match {
            case MayRule => makeState(rhs1, _)
            case MustRule => makeState(_, rhs1)
          }
        }
        addToWorklist(makeRule(rhs))
      }
    }
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

  def combine(lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]) {
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = AttackRule.makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal,
          lhsRule.rhsCall, lhsRule.rhsCallMap)
      //println("Combined rule " + rule + " from " + lhsRule + " and " + rhsRule)
      addToWorklist(rule)
    }
    lhsRule.rhsCallMap.get(rhsRule.lhs) foreach { callTails =>
      callTails foreach { callTail =>
        val newCallTails = callTails - callTail
        val newRhsCall = if(newCallTails.isEmpty) {
            lhsRule.rhsCallMap - rhsRule.lhs
          }
          else {
            lhsRule.rhsCallMap + ((rhsRule.lhs, newCallTails))
          }
        val newRhsInternal =
          lhsRule.rhsInternal | (rhsRule.rhsReturn map { rhs => rhs + callTail })
        val rule = AttackRule.makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal, newRhsCall)
        //println("Combined rule " + rule + " from " + lhsRule + " and " + rhsRule)
        addToWorklist(rule)
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
  def testRefinement(initial: InternalState[A]): Boolean = {
    addRulesFromState(initial)
    var counter = 0
    var obsolete = 0
    while(workingList.nonEmpty) {
      // get rule from worklist
      counter += 1
      val rule = workingList.dequeue
      if((counter < 50) || (counter < 100 && counter % 10 == 0) || (counter < 1000 && counter % 100 == 0) || counter % 1000 == 0) {
        //println("Got from worklist rule num " + counter)
        //println("Num of all rules: " + ((0, 0) /: allMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Num of rhs rules: " + ((0, 0) /: rhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Num of lhs rules: " + ((0, 0) /: lhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        //println("Number of obsolete rules is " + obsolete)
        println("Cur rule " + rule + "; num " + counter + "; total number of rules " + numRules + "; number of obsolete rules " + obsolete)
      }
      // check if winning strategy for attacker has been found
      if(rule.lhs == initial && rule.size == 0) {
        //println("Found winning strategy " + rule)
        return false
      }
      else if(addRule(rule)) {
        rule match {
          case lhsRule @ LhsAttackRule(_,_,rhsInternal,_,rhsCallMap) =>
            for{ lhsRhs <- (rhsInternal | rhsCallMap.keySet) } {
              addRulesFromState(lhsRhs)
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
      else {
        obsolete += 1
      }
    }
    // no winning strategy for attacker found, so the states refine
    //println("Total number of rules is " + numRules)
    //println("Number of obsolete rules is " + obsolete)
    return true
  }
}
