import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.TreeSet
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.PriorityQueue

/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
abstract sealed class AttackRule[A] {
  val lhs: (A, A)
  val rhsInternal: Set[(A, A)]
  val rhsCall: Map[(A, A), Set[A]]
  val rhsReturn: Set[A]
  lazy val rhs = (rhsInternal map { rhs => List(rhs._1, rhs._2) }) |
            (rhsCall flatMap { rhs => rhs._2 map { List(rhs._1._1, rhs._1._2, _) } }).toSet |
            (rhsReturn map { rhs => List(rhs) })
  override def toString =
    lhs.toString + " -> " +
    rhsInternal.mkString("{",",","}") +
    rhsReturn.mkString("{",",","}") +
    (rhsCall map { e => e._1 + e._2.mkString("(",",",")") }).mkString("{",",","}")
}
case class LhsAttackRule[A](lhs: (A, A), rhsInternal: Set[(A, A)], rhsCall: Map[(A, A), Set[A]], rhsReturn: Set[A]) extends AttackRule[A] {
  override val hashCode = scala.runtime.ScalaRunTime._hashCode(LhsAttackRule.this)
}
case class RhsAttackRule[A](lhs: (A, A), rhsReturn: Set[A]) extends AttackRule[A] {
  val rhsInternal = Set.empty[(A, A)]
  val rhsCall = Map.empty[(A, A), Set[A]]
  override val hashCode = scala.runtime.ScalaRunTime._hashCode(RhsAttackRule.this)
}
object AttackRule {
  private def partition[A](rhs: Set[List[A]]) = {
    val (rhsReturnFull, rhsCallInternal) = rhs partition { _.size < 2 }
    val rhsReturn = rhsReturnFull map { _(0) }
    val (rhsInternalFull, rhsCallFull) = rhsCallInternal partition { _.size < 3 }
    val rhsInternal = rhsInternalFull map { rhs => (rhs(0), rhs(1)) }
    var rhsCall = Map[(A, A), Set[A]]()
    rhsCallFull foreach { rhs =>
      val head = (rhs(0), rhs(1))
      val tail = rhs(2)
      val entry = rhsCall.get(head) match {
        case Some(list) => list + tail
        case None => Set(tail)
      }
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
    /*val calls = y.rhsReturn.size compare x.rhsReturn.size
    if(calls != 0) {
      calls
    }
    else {
      val internals = y.rhsInternal.size compare x.rhsInternal.size
      if(internals != 0) {
        internals
      }
      else {
        y.rhsCall.size compare x.rhsCall.size
      }
    }*/
    //(y.rhsReturn.size + y.rhsInternal.size + y.rhsCall.size) compare (x.rhsReturn.size + x.rhsInternal.size + x.rhsCall.size)
  }
}

class RefinementTester[B](mprs: MPRS[B]) {
  type A = (B, B)

  val workingSet = new PriorityQueue[AttackRule[A]]()(new RuleOrdering())
  //val workingLhs = new HashSet[AttackRule[A]]()
  //val workingRhs = new HashSet[AttackRule[A]]()
  //val workingSet = new HashSet[AttackRule[A]]()
  //val workingSet = new TreeSet[AttackRule[A]]()(Ordering.by(_.rhs.size))
  val stateSet = new HashSet[(A, A)]()

  val allMap = new HashMap[(A, A), Set[AttackRule[A]]]()
  val rhsMap = new HashMap[(A, A), Set[RhsAttackRule[A]]]()
  val lhsMap = new HashMap[(A, A), Set[LhsAttackRule[A]]]()

  def addRulesFrom(lhs: (A, A)) {
    if(stateSet.add(lhs)) {
      println("Added new starting state " + lhs)
      allMap += ((lhs, Set.empty[AttackRule[A]]))
      rhsMap += ((lhs, Set.empty[RhsAttackRule[A]]))
      lhsMap += ((lhs, Set.empty[LhsAttackRule[A]]))
      val attackSet = getAttacksFrom(lhs)
      attackSet foreach { add(_) }
    }
  }

  def delete(rule: AttackRule[A]) {
    //workingSet -= rule
    //workingLhs -= rule
    //workingRhs -= rule
    allMap += ((rule.lhs, allMap(rule.lhs) - rule))
    rule match {
      case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) => 
        rhsInternal foreach { rhs =>
          lhsMap += ((rhs, lhsMap(rhs) - lhsRule))
        }
        rhsCall.keySet foreach { rhs =>
          lhsMap += ((rhs, lhsMap(rhs) - lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap(lhs) - rhsRule))
    }
  }

  def ruleIncluded(oldRule: AttackRule[A], newRule: AttackRule[A]) = {
    oldRule.lhs == newRule.lhs &&
    oldRule.rhs.subsetOf(newRule.rhs)
    /*oldRule.rhsReturn.subsetOf(newRule.rhsReturn) &&
    oldRule.rhsInternal.subsetOf(newRule.rhsInternal) &&
    (oldRule.rhsCall forall { entry =>
      entry._2.subsetOf(newRule.rhsCall.getOrElse(entry._1, Set.empty))
    })*/
  }

  private def addNew(rule: AttackRule[A]) {
    workingSet += rule
    allMap += ((rule.lhs, allMap(rule.lhs) + rule))
    rule match {
      case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) => 
        rhsInternal foreach { rhs =>
          addRulesFrom(rhs)
          lhsMap += ((rhs, lhsMap(rhs) + lhsRule))
        }
        rhsCall.keySet foreach { rhs =>
          addRulesFrom(rhs)
          lhsMap += ((rhs, lhsMap(rhs) + lhsRule))
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap(lhs) + rhsRule))
    }
  }

  def add(rule: AttackRule[A]): Boolean = {
    //TODO comment
    val rules = allMap(rule.lhs)
    if(rules exists { ruleIncluded(_, rule) }) { //TODO: combine with second part?
      false
    }
    else {
      val delSet = (rules filter { ruleIncluded(rule, _) })
      delSet foreach { delete(_) }
      addNew(rule)
      true
    }
  }
  
  /**
   * Get all the attacks that are possible from a state under
   * the given mPRS.
   * @param lhs the paired state from which the attack is done
   * @param mprs the original mPRS with the transition rules
   * @return a list of AttackRules starting from the given state
   */ 
  def getAttacksFrom(lhs: ((B, B), (B, B))) = {
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
        case MayRule => (rhs2list map { rhs1 zip _ }).toSet
        case MustRule => (rhs2list map { _ zip rhs1 }).toSet
      }
      //println("Made attack " + lhs + " -> " + rhs3)
      val rule = AttackRule.makeRule(lhs, rhs3)
      //println("Got attack " + rule)
      rule
    }
  }

  def combine(lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]) = {
    if(lhsRule.rhsInternal.contains(rhsRule.lhs)) {
      val newRhsInternal = lhsRule.rhsInternal - rhsRule.lhs
      val newRhsReturn = lhsRule.rhsReturn | rhsRule.rhsReturn
      val rule = AttackRule.makeRule(lhsRule.lhs, newRhsReturn, newRhsInternal, lhsRule.rhsCall)
      //println("Combined " + lhsRule + " and " + rhsRule + " to " + rule)
      add(rule)
    }
    val tail = lhsRule.rhsCall.getOrElse(rhsRule.lhs, Set.empty[A])
    tail foreach { rhsTail => //TODO optimize
      val newTail = tail - rhsTail
      val newRhsCall = if(newTail.isEmpty) lhsRule.rhsCall - rhsRule.lhs
        else lhsRule.rhsCall + ((rhsRule.lhs, newTail))
      val newRhsInternal = lhsRule.rhsInternal | (rhsRule.rhsReturn map ( (_, rhsTail) ))
      val rule = AttackRule.makeRule(lhsRule.lhs, lhsRule.rhsReturn, newRhsInternal, newRhsCall)
      //println("Combined " + lhsRule + " and " + rhsRule + " to " + rule)
      add(rule)
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
    /*if(!isVPDA(mprs)) {
      throw new IllegalArgumentException("Given mPRS is not a vPDA")
    */
    // encode all states as pairs (lhs, rhs)
    val initialList = mprs.initialLHS.toList zip mprs.initialRHS.toList
    val initial = (initialList(0), initialList(1))
    // initialize rules with rules from initial state
    addRulesFrom(initial)
    var counter = 0
    var obsolete = 0
    var maxsize = 0
    var prevtime = 0L
    while(workingSet.nonEmpty) {
      // get rule from worklist
      counter += 1
      //val rule = workingSet.firstKey
      //val curWorkingSet = if(workingRhs.nonEmpty) workingRhs else workingLhs
      //val rule = curWorkingSet.head
      //curWorkingSet -= rule
      val rule = workingSet.dequeue
      //workingSet -= rule
      val size = rule.rhsReturn.size + rule.rhsInternal.size
      if(size > maxsize) {
        maxsize = size
        println("Max size of rhs is " + maxsize)
      }
      if((counter < 10) || (counter < 100 && counter % 10 == 0) || (counter < 1000 && counter % 100 == 0) || counter % 1000 == 0) {
        println("Got from worklist rule num " + counter)
        //println("All rules: " + allMap)
        //println("Rhs rules: " + rhsMap)
        //println("Lhs rules: " + lhsMap)
        println("Num of all rules: " + ((0, 0) /: allMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Num of rhs rules: " + ((0, 0) /: rhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Num of lhs rules: " + ((0, 0) /: lhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Max size of rhs is " + maxsize)
        println("Number of obsolete rules is " + obsolete)
        println("Cur rule is " + rule)
      }
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.rhsInternal.isEmpty &&
         rule.rhsReturn.isEmpty && rule.rhsCall.isEmpty) {
        println("Found winning strategy " + rule)
        return false
      }
      else if(allMap(rule.lhs) exists { oldrule =>
        ruleIncluded(oldrule, rule) && !ruleIncluded(rule, oldrule) } ) {
        //println("Rule already obsolete: " + rule)
        obsolete += 1
      }
      else {
        rule match {
          case lhsRule @ LhsAttackRule(_,rhsInternal,rhsCall,_) =>
            for{ lhsRhs <- (rhsInternal | rhsCall.keySet) } {
              for{ rhsRule <- rhsMap(lhsRhs) } {
                combine(lhsRule, rhsRule)
              }
            }
          case rhsRule @ RhsAttackRule(lhs,_) =>
            for{ lhsRule <- lhsMap(lhs) } {
              combine(lhsRule, rhsRule)
            }
        }
      }
    }
    // no winning strategy for attacker found, so the states refine
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
