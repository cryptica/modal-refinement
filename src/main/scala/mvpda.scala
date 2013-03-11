import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.LinkedHashSet

/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
case class AttackRule[A](lhs: List[A], rhs: Set[List[A]]) {
  override def toString =
    lhs.mkString + " -> " +(rhs map { _.mkString }).mkString("{",",","}")
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
   *         or a more specific element 
   */
  def add(key: List[A], elem: Elem): Boolean = {
    rules.get(key) match {
      case Some(elemlist) =>
        if(elemlist exists { elemIncluded(_, elem) }) false
        else {
          rules.put(key, elem :: elemlist)
          true
        }
      case None =>
        rules.put(key, List(elem))
        true
    }
  }
  
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
      AttackRule(lhs, rhs3)
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
  def testRefinement[B](mprs: MPRS[B]): Boolean = {
    if(!isVPDA(mprs)) {
      throw new IllegalArgumentException("Given mPRS is not a vPDA")
    }
    // encode all states as pairs (lhs, rhs)
    type A = (B, B)
    val initial = mprs.initialLHS.toList zip mprs.initialRHS.toList
    // the set containing all the rules generated
    val ruleSet = new HashSet[AttackRule[A]]()
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
      if(!ruleSet.contains(rule)) {
        if(!worklist.contains(rule)) {
          worklist += rule
        }
        ruleSet += rule
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
    while(worklist.nonEmpty) {
      // get rule from worklist
      val rule = worklist.head
      println("Got from worklist rule " + rule)
      worklist -= rule
      // check if winning strategy for attacker is already found
      if(rule.lhs == initial && rule.rhs.isEmpty) {
        println("Found winning strategy " + rule)
        return false
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
    return true
  }
  
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
