
/*case class State[A, +S <: MVPDAState[A]](left: S, right: S) {
  def swap: State[A, S] = State(right, left)
  override def toString = "(" + left + "," + right + ")"
}*/

abstract sealed class State[A] {
  type S <: MVPDAState[A]
  val left: S
  val right: S
  override def toString = "(" + left + "," + right + ")"
}
case class ReturnState[A](left: Return[A], right: Return[A]) extends State[A] {
  type S = Return[A]
  def +(that: ReturnState[A]): InternalState[A] =
    InternalState(left + that.left, right + that.right)
}
case class InternalState[A](left: Internal[A], right: Internal[A]) extends State[A] {
  type S = Internal[A]
  def swap = InternalState(right, left)
  def +(that: ReturnState[A]): CallState[A] =
    CallState(left + that.left, right + that.right)
}
case class CallState[A](left: Call[A], right: Call[A]) extends State[A] {
  type S = Call[A]
}

/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
abstract sealed class AttackRule[A] {
  val lhs: InternalState[A]
  val rhs: Set[State[A]]
  def size = rhs.size
  override def toString = lhs.toString + " -> " + rhs.mkString("{",",","}")
  def <=(that: AttackRule[A]) = (lhs == that.lhs) && (rhs subsetOf that.rhs)
}

case class LhsAttackRule[A](
    lhs: InternalState[A],
    rhsReturn: Set[ReturnState[A]],
    rhsInternal: Set[InternalState[A]],
    rhsCall: Set[CallState[A]],
    rhsCallMap: Map[InternalState[A], Set[ReturnState[A]]]
  ) extends AttackRule[A] {
  val rhs = Set.empty[State[A]] ++ rhsReturn ++ rhsInternal ++ rhsCall
  override def <=(that: AttackRule[A]) = that match {
    case RhsAttackRule(_,rhsReturn) => false
    case LhsAttackRule(thatLhs,thatRhsReturn,thatRhsInternal,thatRhsCall,_) =>
      (lhs == thatLhs) &&
      (rhsReturn subsetOf thatRhsReturn) &&
      (rhsInternal subsetOf thatRhsInternal) &&
      (rhsCall subsetOf thatRhsCall)
  }
}

case class RhsAttackRule[A](
    lhs: InternalState[A],
    rhsReturn: Set[ReturnState[A]]
  ) extends AttackRule[A] {
  val rhs = Set.empty[State[A]] ++ rhsReturn
  override def <=(that: AttackRule[A]) =
    lhs == that.lhs &&
    (that match {
      case RhsAttackRule(_,thatRhsReturn) =>
        (rhsReturn subsetOf thatRhsReturn)
      case LhsAttackRule(_,thatRhsReturn,_,_,_) =>
        (rhsReturn subsetOf thatRhsReturn)
    })
}

object AttackRule {
  def makeReturnRule[A](
    lhs: InternalState[A],
    rhsReturn: Set[ReturnState[A]]
  ): AttackRule[A] = 
  makeRule(lhs, rhsReturn, Set.empty, Map.empty)

  def makeInternalRule[A](
    lhs: InternalState[A],
    rhsInternal: Set[InternalState[A]]
  ): AttackRule[A] = 
  makeRule(lhs, Set.empty, rhsInternal, Map.empty)

  def makeCallRule[A](
    lhs: InternalState[A],
    rhsCallSet: Set[CallState[A]]
  ): AttackRule[A] = {
    var rhsCall = Map[InternalState[A], Set[ReturnState[A]]]()
    rhsCallSet foreach { rhs =>
      val head = InternalState[A](rhs.left.head, rhs.right.head)
      val tail = ReturnState[A](rhs.left.tail, rhs.right.tail)
      rhsCall += ((head, rhsCall.getOrElse(head, Set.empty) + tail))
    }
    makeRule(lhs, Set.empty, Set.empty, rhsCall)
  }
  
  def makeRule[A](
    lhs: InternalState[A],
    rhsReturn: Set[ReturnState[A]],
    rhsInternal: Set[InternalState[A]],
    rhsCallMap: Map[InternalState[A], Set[ReturnState[A]]]
  ): AttackRule[A] = {
    val rhsCall = (rhsCallMap flatMap { entry => entry._2 map { tail => entry._1 + tail } }).toSet
    makeRule(lhs, rhsReturn, rhsInternal, rhsCall, rhsCallMap)
  }
  
  def makeRule[A](
    lhs: InternalState[A],
    rhsReturn: Set[ReturnState[A]],
    rhsInternal: Set[InternalState[A]],
    rhsCall: Set[CallState[A]],
    rhsCallMap: Map[InternalState[A], Set[ReturnState[A]]]
  ): AttackRule[A] = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule[A](lhs, rhsReturn)
    }
    else {
      LhsAttackRule[A](lhs, rhsReturn, rhsInternal, rhsCall, rhsCallMap)
    }
  }
}

