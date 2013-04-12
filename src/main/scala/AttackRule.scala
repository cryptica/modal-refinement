
case class State[A, +S <: MVPDAState[A]](left: S, right: S) {
  def swap: State[A, S] = State(left, left)
  override def toString = "(" + left + "," + right + ")"
}

/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
abstract sealed class AttackRule[A] {
  val lhs: State[A, Internal[A]]
  val rhs: List[State[A, MVPDAState[A]]]
  def makeRhs(list: Seq[State[A, MVPDAState[A]]]) = list
  val size: Int
  override def toString = lhs.toString + " -> " + rhs.mkString("{",",","}")
}

case class LhsAttackRule[A](
    lhs: State[A, Internal[A]],
    rhsReturn: Set[State[A, Return[A]]],
    rhsInternal: Set[State[A, Internal[A]]],
    rhsCall: Map[State[A, Internal[A]], Set[State[A, Return[A]]]]
  ) extends AttackRule[A] {
  override val hashCode = 41*(41*(41*(41 + lhs.hashCode) + rhsInternal.hashCode) + rhsCall.hashCode) + rhsReturn.hashCode
  val callComplete =
    (rhsCall flatMap { entry =>
      val head = entry._1
      val tails = entry._2
      tails map { tail => (head.left + tail.left, head.right + tail.right) }
    }).toSet
  val size = rhsInternal.size + rhsCall.size + callComplete.size
  lazy val rhs = rhsReturn.toList// ++ rhsInternal.toList ++ callComplete.toList
}

case class RhsAttackRule[A](
    lhs: State[A, Internal[A]],
    rhsReturn: Set[State[A, Return[A]]]
  ) extends AttackRule[A] {
  override val hashCode = 31*(31 + lhs.hashCode) + rhsReturn.hashCode
  val size = rhsReturn.size
  lazy val rhs = rhsReturn.toList
}

object AttackRule {
  def makeReturnRule[A](
    lhs: State[A, Internal[A]],
    rhsReturn: Set[State[A, Return[A]]]
  ): AttackRule[A] = 
  makeRule(lhs, rhsReturn, Set.empty, Map.empty)

  def makeInternalRule[A](
    lhs: State[A, Internal[A]],
    rhsInternal: Set[State[A, Internal[A]]]
  ): AttackRule[A] = 
  makeRule(lhs, Set.empty, rhsInternal, Map.empty)

  def makeCallRule[A](
    lhs: State[A, Internal[A]],
    rhsCallSet: Set[State[A, Call[A]]]
  ): AttackRule[A] = {
    var rhsCall = Map[State[A, Internal[A]], Set[State[A, Return[A]]]]()
    rhsCallSet foreach { rhs =>
      val head = State[A, Internal[A]](rhs.left.head, rhs.right.head)
      val tail = State[A, Return[A]](rhs.left.tail, rhs.right.tail)
      rhsCall += ((head, rhsCall.getOrElse(head, Set.empty) + tail))
    }
    makeRule(lhs, Set.empty, Set.empty, rhsCall)
  }

  /*def makeRule[A](
    lhs: State[A, Internal[A]],
    rhs: State[A, MVPDAState[A]]
  ): AttackRule[A] = {

  }*/
  def makeRule[A](
    lhs: State[A, Internal[A]],
    rhsReturn: Set[State[A, Return[A]]],
    rhsInternal: Set[State[A, Internal[A]]],
    rhsCall: Map[State[A, Internal[A]], Set[State[A, Return[A]]]]
  ): AttackRule[A] = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule[A](lhs, rhsReturn)
    }
    else {
      LhsAttackRule[A](lhs, rhsReturn, rhsInternal, rhsCall)
    }
  }
}

