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
  val lhs: List[A]
  val rhsInternal: Set[List[A]]
//  val rhsCall: Set[Map[List[A], A]]
  val rhsReturn: Set[A]
  override def toString =
    lhs.mkString + " -> " + (rhsInternal map { _.mkString }).mkString("{",",","}") + rhsReturn.mkString("{",",","}")
}
case class LhsAttackRule[A](lhs: List[A], rhsInternal: Set[List[A]], rhsReturn: Set[A]) extends AttackRule[A] {
}
case class RhsAttackRule[A](lhs: List[A], rhsReturn: Set[A]) extends AttackRule[A] {
  val rhsInternal = Set.empty[List[A]]
//  val rhsCall = Set.empty[Map[List[A], A]]
}
object AttackRule {
  private def partition[A](rhs: Set[List[A]]) = {
    val (rhsReturnFull, rhsInternal) = rhs partition { _.size < 2 }
    val rhsReturn = rhsReturnFull map { _(0) }
    (rhsReturn, rhsInternal)
  }

  private def makeFromPartition[A](lhs: List[A], rhsReturn: Set[A], rhsInternal: Set[List[A]]) = {
    if(rhsInternal.isEmpty) {
      RhsAttackRule(lhs, rhsReturn)
    }
    else {
      LhsAttackRule(lhs, rhsInternal, rhsReturn)
    }
  }


  def makeRule[A](lhs: List[A], rhs: Set[List[A]]): AttackRule[A] = {
    val (rhsReturn, rhsInternal) = partition(rhs)
    makeFromPartition(lhs, rhsReturn, rhsInternal)
  }

  def combine[A](lhsRule: LhsAttackRule[A], rhsRule: RhsAttackRule[A]): Set[AttackRule[A]]  = {
    for{ lhsRhs <- lhsRule.rhsInternal
      lhsRhsHead = lhsRhs.take(2)
      if lhsRhsHead == rhsRule.lhs
      lhsRhsTail = lhsRhs.drop(2)
      lhsRhsRest = lhsRule.rhsInternal - lhsRhs
      // add a combined rule for all combinations with rhs rules
      rhsCombined = rhsRule.rhsReturn map { _ :: lhsRhsTail }
      (newRhsReturn, newRhsInternal) = partition(rhsCombined)
      } yield makeFromPartition(lhsRule.lhs, lhsRule.rhsReturn | newRhsReturn, lhsRhsRest | newRhsInternal)
  }
}

class RuleOrdering[A] extends Ordering[AttackRule[A]] {
  override def compare(x: AttackRule[A], y: AttackRule[A]) = {
    (y.rhsReturn.size + y.rhsInternal.size) compare (x.rhsReturn.size + x.rhsInternal.size)
  }
}

class RefinementTester[B](mprs: MPRS[B]) {
  type A = (B, B)

  val workingSet = new PriorityQueue[AttackRule[A]]()(new RuleOrdering())
  //val workingLhs = new HashSet[AttackRule[A]]()
  //val workingRhs = new HashSet[AttackRule[A]]()
  //val workingSet = new HashSet[AttackRule[A]]()
  //val workingSet = new TreeSet[AttackRule[A]]()(Ordering.by(_.rhs.size))
  val stateSet = new HashSet[List[A]]()

  val allMap = new HashMap[List[A], Set[AttackRule[A]]]()
  val rhsMap = new HashMap[List[A], Set[RhsAttackRule[A]]]()
  val lhsMap = new HashMap[List[A], Set[LhsAttackRule[A]]]()

  def addRulesFrom(lhs: List[A]) {
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
      case lhsRule @ LhsAttackRule(_,rhsInternal,_) => 
        rhsInternal foreach { rhs =>
          //if(rhs.length >= 2) {
            val rhsHead = rhs.take(2)
            lhsMap += ((rhsHead, lhsMap(rhsHead) - lhsRule))
          //}
        }
      case rhsRule @ RhsAttackRule(lhs,_) => 
        rhsMap += ((lhs, rhsMap(lhs) - rhsRule))
    }
  }

  def ruleIncluded(oldRule: AttackRule[A], newRule: AttackRule[A]) = {
    oldRule.lhs == newRule.lhs &&
    oldRule.rhsReturn.subsetOf(newRule.rhsReturn) &&
    oldRule.rhsInternal.subsetOf(newRule.rhsInternal)
  }

  private def addNew(rule: AttackRule[A]) {
    workingSet += rule
    allMap += ((rule.lhs, allMap(rule.lhs) + rule))
    rule match {
      case lhsRule @ LhsAttackRule(_,rhsInternal,_) => 
        rhsInternal foreach { rhs =>
          //if(rhs.length >= 2) {
            val rhsHead = rhs.take(2)
            addRulesFrom(rhsHead)
            lhsMap += ((rhsHead, lhsMap(rhsHead) + lhsRule))
          //}
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
  def getAttacksFrom(lhs: List[A]) = {
    val lhsPair = lhs.unzip
    val lhs1 = lhsPair._1
    val lhs2 = lhsPair._2
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
      AttackRule.makeRule(lhs, rhs3)
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
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
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
        println("Num of all rules: " + ((0, 0) /: allMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Num of rhs rules: " + ((0, 0) /: rhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Num of lhs rules: " + ((0, 0) /: lhsMap) {(n,e) => (n._1 + 1, n._2 + e._2.size) })
        println("Max size of rhs is " + maxsize)
        println("Number of obsolete rules is " + obsolete)
        println("Cur rule is " + rule)
      }
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.rhsInternal.isEmpty && rule.rhsReturn.isEmpty) {
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
          case lhsRule @ LhsAttackRule(_,rhsInternal,_) =>
            for{ lhsRhs <- rhsInternal } {
              val lhsRhsHead = lhsRhs.take(2)
              for{ rhsRule <- rhsMap(lhsRhsHead) } {
                (AttackRule.combine(lhsRule, rhsRule)) foreach { add(_) }
              }
            }
          case rhsRule @ RhsAttackRule(lhs,_) =>
            for{ lhsRule <- lhsMap(lhs) } {
              (AttackRule.combine(lhsRule, rhsRule)) foreach { add(_) }
            }
        }
          
            //
//        var isRhsRule = true
        // TODO: eliminate check here
        // check if one right-hand side is a call or internal and
        // therefore the rule is a left-hand side rule
        /*for{ lhsRhs <- rule.rhsInternal } {
//          if(lhsRhs.length >= 2) {
            // seperate rule into parts
            val lhsRhsHead = lhsRhs.take(2)
            val lhsRhsTail = lhsRhs.drop(2)
            val lhsRhsRest = rule.rhsInternal - lhsRhs
            // add a combined rule for all combinations with rhs rules
            for{ rhsRule <- rhsMap(lhsRhsHead) } {
              val newRhs = lhsRhsRest | rule.rhsInternal | (rhsRule.rhsReturn map { _ :: lhsRhsTail })
              add(AttackRule.makeRule(rule.lhs, newRhs))
            }
//            isRhsRule = false
//          }
        }
        // rule only has return righthand sides or none, therefore
        // it can be applied from the right-hand side
        if(rule.isInstanceOf[RhsAttackRule[A]]) {
          val rhsHeads = rule.rhsReturn
          // add a combined rule for all combinations with lhs rules
          for{ lhsRule <- lhsMap(rule.lhs) } {
            for{ lhsRhs <- lhsRule.rhsInternal } {
//              if(lhsRhs.length >= 2) {
                val lhsRhsHead = lhsRhs.take(2)
                if(lhsRhsHead == rule.lhs) {
                  val lhsRhsTail = lhsRhs.drop(2)
                  val lhsRhsRest = lhsRule.rhsInternal - lhsRhs
                  val newRhs = (rhsHeads map { _ :: lhsRhsTail }) | lhsRhsRest | (lhsRule.rhsReturn map { List(_) })
                  add(AttackRule.makeRule(lhsRule.lhs, newRhs))
                }
//              }
            }
          }
        }*/
      }
    }
    // no winning strategy for attacker found, so the states refine
    println("Number of obsolete rules is " + obsolete)
    return true
  }
}

/**
 * This class saves attack rules in a map with the key being a state
 * on the left or right side. On lookup it returns a list of the remaining
 * parts of all the matching attack rules.
 * It may discard some elements on insertion if a more specialized attack
 * rule is already contained.
 */
abstract class AttackRuleMap[A] {
  // the type of the attack rule without the key element
  type Elem
  // map of the keys and list of matching elements
  val rules = new HashMap[List[A], List[Elem]]()

  /**
   * This function should return if a new element to be inserted
   * can already be represented by an old more specialized element
   * already contained in the map and therefore the new element is
   * not needed.
   * @param oldElem the element already contained in the map
   * @param newElem the new element waiting to be inserted
   * @return true if oldElem is a more specialized version
   *         of newElem and therefore newElem can be discarded,
   *         otherwise false
   */
  def elemIncluded(oldElem: Elem, newElem: Elem): Boolean

  /**
   * Adds an element with the given key to the map 
   * @param key the key state
   * @param elem the element
   * @return true if the element was added, false if the same
   *         or a more specific element is already contained
   */
  def add(key: List[A], elem: Elem): Boolean = {
    //TODO comment
    def updateList(list: List[Elem], acc: List[Elem]): Option[List[Elem]] = {
      list match {
        case e :: es =>
          if(elemIncluded(e, elem)) {
            None
          }
          else if(elemIncluded(elem, e)) {
            updateList(es, acc)
          }
          else {
            updateList(es, e :: acc)
          }
        case Nil => Some(elem :: acc)
      }
    }
    updateList(get(key), Nil) match {
      case Some(newlist) => 
        rules.put(key, newlist)
        true
      case None =>
        false
    }
  }

  //def removeOne TODO
  
  def containsExactly(key: List[A], elem: Elem): Boolean =
    get(key) exists { oldElem => elemIncluded(oldElem, elem) && elemIncluded(elem, oldElem) }

  def size = ((0, 0) /: rules) { (size, entry) => (size._1 + 1, size._2 + entry._2.size) }
  
  /**
   * Returns a list of all the elements matching the given key
   * @param key the key state
   * @return a list of all the elements matching that key
   */
  def get(key: List[A]) = rules.get(key) match {
    case Some(elemlist) => elemlist
    case None => Nil
  }
}

/**
 * This class represents a map of rules that can be applied
 * from the left by replacing a state on the right hand side.
 * The key is the state on the right-hand side and the element
 * a tuple of (left-hand side, remaining states after the key state,
 * set of remaining right-hand side rules)
 */
class LhsAttackRuleMap[A] extends AttackRuleMap[A] {
  type Elem = ( List[A], List[A], Set[List[A]] )
  
  override def elemIncluded(oldElem: Elem, newElem: Elem) = {
    oldElem._1 == newElem._1 &&
    oldElem._2 == newElem._2 &&
    oldElem._3.subsetOf(newElem._3)
  }
}

/**
 * This class represents a map of rules that can be applied
 * from the right by replacing a state matching the left-hand side
 * with the right-hand side.
 * The key is the state on the left-hand side and the element is
 * the set of right-hand side states.
 */
class RhsAttackRuleMap[A] extends AttackRuleMap[A] {
  type Elem = Set[A]
    
  override def elemIncluded(oldElem: Elem, newElem: Elem) = {
    oldElem.subsetOf(newElem)
  }
}

// TODO
class GeneralAttackRuleMap[A] extends AttackRuleMap[A] {
  type Elem = Set[List[A]]

  override def elemIncluded(oldElem: Elem, newElem: Elem) = {
    oldElem.subsetOf(newElem)
  }
}

object MVPDA {

  /**
   * Get all the attacks that are possible from a state under
   * the given mPRS.
   * @param lhs the paired state from which the attack is done
   * @param mprs the original mPRS with the transition rules
   * @return a list of AttackRules starting from the given state
   */ 
  def getAttacksFrom[B](lhs: List[(B, B)], mprs: MPRS[B]) = {
    val lhsPair = lhs.unzip
    val lhs1 = lhsPair._1
    val lhs2 = lhsPair._2
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
      AttackRule.makeRule(lhs, rhs3)
    }
  }
  
  def testRefinement[B](mprs: MPRS[B]): Boolean =
    testRefinementNew(mprs)
  
  def testRefinementNew[B](mprs: MPRS[B]): Boolean = {
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
  /*def testRefinementOld[B](mprs: MPRS[B]): Boolean = {
    if(!isVPDA(mprs)) {
      throw new IllegalArgumentException("Given mPRS is not a vPDA")
    }
    // encode all states as pairs (lhs, rhs)
    type A = (B, B)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    // the set containing all the rules generated
    val ruleSet = new GeneralAttackRuleMap[A]()
    // the set containing all the states visited
    val stateSet = new HashSet[List[A]]()
    // the rules that can be applied from the left hand side
    val lhsRules = new LhsAttackRuleMap[A]()
    // the rules that can be applied from the left hand side
    val rhsRules = new RhsAttackRuleMap[A]()
    // worklist of rules generated but not yet applied
    val worklist = new LinkedHashSet[AttackRule[A]]()
    // adds the rule to the worklist if it was not already added
    def addRule(rule: AttackRule[A]) {
      if(ruleSet.add(rule.lhs, rule.rhs)) {
        worklist.add(rule)
      }
    }
    // adds all the basic attack rules from a state if it is new
    def addRulesFrom(lhs: List[A]) {
      if(stateSet.add(lhs)) {
        println("Added new starting state " + lhs)
        getAttacksFrom(lhs, mprs) foreach { addRule(_) }
      }
    }
    // initialize rules with rules from initial state
    addRulesFrom(initial)
    var counter = 0
    var obsolete = 0
    var maxsize = 0
    while(worklist.nonEmpty) {
      // get rule from worklist
      val rule = worklist.last
      worklist -= rule
      counter += 1
      val size = rule.rhs.size
      if(size > maxsize) {
        maxsize = size
        println("Max size of rhs is " + maxsize)
      }
      if(counter % 1000 == 0) {
        println("Got from worklist rule num " + counter)
        println("Num of all rules: " + ruleSet.size)
        println("Num of rhs rules: " + rhsRules.size)
        println("Num of lhs rules: " + lhsRules.size)
        println("Cur size of rhs is " + rule.rhs.size)
        println("Number of obsolete rules is " + obsolete)
        println("Cur rule is " + rule)
      }
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.rhs.isEmpty) {
        println("Found winning strategy " + rule)
        return false
      }
      else if(!ruleSet.containsExactly(rule.lhs, rule.rhs)) {
        //println("Rule already obsolete: " + rule)
        obsolete += 1
      }
      else {
        var isRhsRule = true
        // check if one right-hand side is a call or internal and
        // therefore the rule is a left-hand side rule
        for{ lhsRhs <- rule.rhs } {
          if(lhsRhs.length >= 2) {
            // seperate rule into parts
            val lhsRhsHead = lhsRhs.take(2)
            val lhsRhsTail = lhsRhs.drop(2)
            val lhsRhsRest = rule.rhs - lhsRhs
            // could have found new reachable state
            addRulesFrom(lhsRhsHead)
            // add new left-hand side rule
            if(lhsRules.add(lhsRhsHead, (rule.lhs, lhsRhsTail, lhsRhsRest))) {
              // add a combined rule for all combinations with rhs rules
              for{ rhsSet <- rhsRules.get(lhsRhsHead) } {
                val newRhs = lhsRhsRest | (rhsSet map { _ :: lhsRhsTail })
                addRule(AttackRule(rule.lhs, newRhs))
              }
            }
            isRhsRule = false
          }
        }
        // rule only has return righthand sides or none, therefore
        // it can be applied from the right-hand side
        if(isRhsRule) {
          // add new right-hand side rule
          val rhsHeads = rule.rhs map { _(0) }
          if(rhsRules.add(rule.lhs, rhsHeads)) {
            // add a combined rule for all combinations with lhs rules
            for{ (lhs, rhsTail, rhsRest) <- lhsRules.get(rule.lhs) } {
              val newRhs = (rhsHeads map { _ :: rhsTail }) | rhsRest
              addRule(AttackRule(lhs, newRhs))
            }
          }
        }
      }
    }
    // no winning strategy for attacker found, so the states refine
    println("Number of obsolete rules is " + obsolete)
    return true
  }*/
  
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
