import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.PriorityQueue

class RefinementTester[A](mvpda: MVPDA[A]) {
  type State = (Return[A], Return[A])
  type LHS = (Internal[A], Internal[A])

  val workingSet = new PriorityQueue[AttackRule[A]]()(Ordering.by{ rule => -(rule.size) })
  val stateSet = new HashSet[LHS]()

  val allMap = new HashMap[LHS, Set[AttackRule[A]]]()
  val rhsMap = new HashMap[LHS, Set[RhsAttackRule[A]]]()
  val lhsMap = new HashMap[LHS, Set[LhsAttackRule[A]]]()
  var numRules = 0
  

  def addRulesFrom(lhs: LHS) {
    if(stateSet.add(lhs)) {
      //println("New lhs " + lhs)
      addAttacksFrom(lhs)
    }
  }

  def ruleIncluded(oldRule: AttackRule[A], newRule: AttackRule[A]) = {
    oldRule.lhs == newRule.lhs &&
    ((oldRule, newRule) match {
      case (lhs1 @ LhsAttackRule(_,rhsReturn1,rhsInternal1,_),
            lhs2 @ LhsAttackRule(_,rhsReturn2,rhsInternal2,_)) =>
        rhsReturn1.subsetOf(rhsReturn2) && rhsInternal1.subsetOf(rhsInternal2) &&
        lhs1.callComplete.subsetOf(lhs2.callComplete)
      case (RhsAttackRule(_,rhsReturn1), LhsAttackRule(_,rhsReturn2,_,_)) =>
        rhsReturn1.subsetOf(rhsReturn2)
      case (RhsAttackRule(_,rhsReturn1), RhsAttackRule(_,rhsReturn2)) =>
        rhsReturn1.subsetOf(rhsReturn2)
      case _ => false
    })
  }

  private def addNewRule(rule: AttackRule[A]): Boolean = {
    var rules = allMap.getOrElse(rule.lhs, Set.empty)
    // Remove bigger rules
    rules foreach { oldRule =>
      if(ruleIncluded(oldRule, rule)) {
        return false
      }
      if(ruleIncluded(rule, oldRule)) {
        rules -= oldRule
        numRules -= 1
        oldRule match {
          case lhsRule @ LhsAttackRule(_,_,rhsInternal,rhsCall) => 
            (rhsInternal | rhsCall.keySet) foreach { rhs =>
              lhsMap += ((rhs, lhsMap(rhs) - lhsRule))
            }
          case rhsRule @ RhsAttackRule(lhs,_) => 
            rhsMap += ((lhs, rhsMap(lhs) - rhsRule))
        }
      }
    }
    allMap += ((rule.lhs, rules + rule))
    numRules += 1
    rule match {
      case lhsRule @ LhsAttackRule(_,_,rhsInternal,rhsCall) => 
        (rhsInternal | rhsCall.keySet) foreach { rhs =>
          lhsMap += ((rhs, lhsMap.getOrElse(rhs, Set.empty) + lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap.getOrElse(lhs, Set.empty) + rhsRule))
    }
    return true
  }

  def add(rule: AttackRule[A]) {
    val rules = allMap.getOrElse(rule.lhs, Set.empty)
    if(!(rules exists { ruleIncluded(_, rule) })) {
      workingSet += rule
    }
  }
  
  /**
   * Get all the attacks that are possible from a state under
   * the given mPRS.
   * @param lhs the paired state from which the attack is done
   * @param mprs the original mPRS with the transition rules
   * @return a list of AttackRules starting from the given state
   */ 
  def addAttacksFrom(lhs: LHS) {
    def makeRuleFrom[B](
      rulesMap: Map[(String, RuleType), Map[Internal[A], Set[B]]]
    )(makeRule: Set[(B, B)] => AttackRule[A]) = {
      for {
        ((_, ruleType), rhsMap) <- rulesMap
        (lhs1, lhs2) = ruleType match {
          case MayRule => lhs
          case MustRule => lhs.swap
        }
        rhs1 <- rhsMap.getOrElse(lhs1, Set.empty)
        rhs2list = rhsMap.getOrElse(lhs2, Set.empty)
      } {
        val rhs = ruleType match {
          case MayRule => rhs2list map { (rhs1, _) }
          case MustRule => rhs2list map { (_, rhs1) }
        }
        add(makeRule(rhs))
      }
    }
    makeRuleFrom(mvpda.returnRules) { AttackRule.makeReturnRule(lhs, _) }
    makeRuleFrom(mvpda.internalRules) { AttackRule.makeInternalRule(lhs, _) }
    makeRuleFrom(mvpda.callRules) { rhs =>
      AttackRule.makeCallRule(lhs, rhs)
    }
  }

  def combine(lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]) {
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
          (rhsRule.rhsReturn map { rhs => ((rhs._1 + callTail._1), (rhs._2 + callTail._2)) })
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
    addRulesFrom(mvpda.initial)
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
        println("Cur rule " + rule + "; num " + counter + "; total number of rules " + numRules + "; number of obsolete rules " + obsolete)
      }
      // check if winning strategy for attacker has been found
      if(rule.lhs == mvpda.initial && rule.size == 0) {
        //println("Found winning strategy " + rule)
        return false
      }
      else if(addNewRule(rule)) {
        rule match {
          case lhsRule @ LhsAttackRule(_,_,rhsInternal,rhsCall) =>
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
