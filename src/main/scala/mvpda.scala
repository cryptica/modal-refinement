import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.TreeSet
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.PriorityQueue
import scala.collection.mutable.Queue


class RefinementTester[A](mprs: MPRS[A]) {
  type State = (A, A)
  type Internal = (State, State)

  /**
   * This class encodes a single or combined attack moves
   * with all the possible results from applying defending moves.
   * @param lhs the origin state
   * @param rhs the set of possible destination states
   */
  abstract sealed class AttackRule {
    val lhs: Internal
    val rhs: Set[(List[A], List[A])]
    val size: Int
    override def toString =
      lhs.toString + " -> " + (rhs map { r => "(" + r._1.mkString(".") + "," + r._2.mkString(".") + ")" }).mkString("{",",","}")
  }
  case class LhsAttackRule(lhs: Internal, rhsReturn: Set[State], rhsInternal: Set[Internal], rhsCall: Map[Internal, Set[State]]) extends AttackRule {
    override val hashCode = 41*(41*(41*(41 + lhs.hashCode) + rhsInternal.hashCode) + rhsCall.hashCode) + rhsReturn.hashCode
    val callComplete = (rhsCall flatMap { rhs => rhs._2 map { r => ((rhs._1._1._1, rhs._1._1._2, r._1), (rhs._1._2._1, rhs._1._2._2, r._2)) } }).toSet
    val size = rhsInternal.size + rhsCall.size + callComplete.size
    lazy val rhs =
      (rhsReturn map { rhs => (List(rhs._1), List(rhs._2)) }) |
      (rhsInternal map { rhs => (List(rhs._1._1, rhs._1._2), List(rhs._2._1, rhs._2._2)) }) |
      (callComplete map { rhs => (List(rhs._1._1, rhs._1._2, rhs._1._3), List(rhs._2._1, rhs._2._2, rhs._2._3)) })
  }
  case class RhsAttackRule(lhs: Internal, rhsReturn: Set[State]) extends AttackRule {
    override val hashCode = 31*(31 + lhs.hashCode) + rhsReturn.hashCode
    val size = rhsReturn.size
    lazy val rhs = (rhsReturn map { rhs => (List(rhs._1), List(rhs._2)) })
  }

  val workingSet = new PriorityQueue[AttackRule]()(Ordering.by{ rule => -(rule.size) })
  val stateSet = new HashSet[Internal]()

  val allMap = new HashMap[Internal, Set[AttackRule]]()
  val rhsMap = new HashMap[Internal, Set[RhsAttackRule]]()
  val lhsMap = new HashMap[Internal, Set[LhsAttackRule]]()
  var numRules = 0
  
  val initial = {
    (mprs.initialLeft, mprs.initialRight) match {
      case (Const(p1) +: Const(p2), Const(q1) +: Const(q2)) =>
        ((p1, p2), (q1, q2))
      case _ =>
        throw new IllegalArgumentException("Given mPRS is not an mvPDA")
    }
  }
  val returnRules = new HashMap[(String, RuleType), Map[State, Set[A]]]()
  val internalRules = new HashMap[(String, RuleType), Map[State, Set[State]]]()
  val callRules = new HashMap[(String, RuleType), Map[State, Set[(State, A)]]]()
  makeVPDA()
  
  /**
   * Test if the given modal process rewrite system is
   * a visible PDA. An mPRS is a vPDA if the actions can
   * be partitioned into three sets for internal, call or
   * return actions.
   * @param mprs the mPRS to be tested
   * @return true if the mPRS is a vPDA, otherwise false
   */ 
  private def makeVPDA() {
    mprs.rules foreach { rule => rule match {
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1)) =>
        val curRules = returnRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse((l1, l2), Set.empty)
        returnRules += (((a, rt), curRules + (((l1, l2), curSet + r1))))
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1) +: Const(r2)) =>
        val curRules = internalRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse((l1, l2), Set.empty)
        internalRules += (((a, rt), curRules + (((l1, l2), curSet + ((r1, r2))))))
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1) +: Const(r2) +: Const(r3)) =>
        val curRules = callRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse((l1, l2), Set.empty)
        callRules += (((a, rt), curRules + (((l1, l2), curSet + (((r1, r2), r3))))))
      case _ =>
        throw new IllegalArgumentException("Given mPRS is not an mvPDA")
      }
    }
    val a1 = returnRules.keySet map { _._1 }
    val a2 = internalRules.keySet map { _._1 }
    val a3 = callRules.keySet map { _._1 }
    if((a1 & a2).nonEmpty || (a2 & a3).nonEmpty || (a3 & a1).nonEmpty) {
      throw new IllegalArgumentException("Given mPRS is not an mvPDA")
    }
  }
  
  def makeRule(lhs: Internal, rhsReturn: Set[State], rhsInternal: Set[Internal], rhsCall: Map[Internal, Set[State]]): AttackRule = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule(lhs, rhsReturn)
    }
    else {
      LhsAttackRule(lhs, rhsReturn, rhsInternal, rhsCall)
    }
  }

  def addRulesFrom(lhs: Internal) {
    if(stateSet.add(lhs)) {
      //println("New lhs " + lhs)
      addAttacksFrom(lhs)
    }
  }

  def ruleIncluded(oldRule: AttackRule, newRule: AttackRule) = {
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

  private def addNewRule(rule: AttackRule): Boolean = {
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

  def add(rule: AttackRule) {
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
  def addAttacksFrom(lhs: Internal) {
    def makeRhsFrom[B](rulesMap: HashMap[(String, RuleType), Map[State, Set[B]]]) = {
      for {
        ((_, ruleType), rhsMap) <- rulesMap
        (lhs1, lhs2) = ruleType match {
          case MayRule => lhs
          case MustRule => lhs.swap
        }
        rhs1 <- rhsMap.getOrElse(lhs1, Set.empty)
        rhs2list = rhsMap.getOrElse(lhs2, Set.empty)
      } yield ruleType match {
          case MayRule => rhs2list map { (rhs1, _) }
          case MustRule => rhs2list map { (_, rhs1) }
      }
    }
    makeRhsFrom(returnRules) foreach { rhs =>
      val rule = makeRule(lhs, rhs, Set.empty, Map.empty)
      add(rule)
    }
    makeRhsFrom(internalRules) foreach { rhs =>
      val rule = makeRule(lhs, Set.empty, rhs, Map.empty)
      add(rule)
    }
    makeRhsFrom(callRules) foreach { rhs =>
      var rhsCall = Map[Internal, Set[State]]()
      rhs foreach { rhs =>
        val head = (rhs._1._1, rhs._2._1)
        val tail = (rhs._1._2, rhs._2._2)
        rhsCall += ((head, rhsCall.getOrElse(head, Set.empty) + tail))
      }
      val rule = makeRule(lhs, Set.empty, Set.empty, rhsCall)
      add(rule)
    }
  }

  def combine(lhsRule: LhsAttackRule, rhsRule: RhsAttackRule) {
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal, lhsRule.rhsCall)
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
        val rule = makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal, newRhsCall)
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
        //println("Cur rule " + rule + "; num " + counter + "; total number of rules " + numRules + "; number of obsolete rules " + obsolete)
      }
      // check if winning strategy for attacker has been found
      if(rule.lhs == initial && rule.size == 0) {
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
