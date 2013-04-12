/**
 * This class encodes a single or combined attack moves
 * with all the possible results from applying defending moves.
 * @param lhs the origin state
 * @param rhs the set of possible destination states
 */
abstract sealed class AttackRule[A] {
  val lhs: (Internal[A], Internal[A])
  val rhs: Seq[(MVPDATransition[A], MVPDATransition[A])]
  val size: Int
  override def toString = lhs.toString + " -> " + rhs.mkString("{",",","}")
}

case class LhsAttackRule[A](
    lhs: (Internal[A], Internal[A]),
    rhsReturn: Set[(Return[A], Return[A])],
    rhsInternal: Set[(Internal[A], Internal[A])],
    rhsCall: Map[(Internal[A], Internal[A]), Set[(Return[A], Return[A])]]
  ) extends AttackRule[A] {
  override val hashCode = 41*(41*(41*(41 + lhs.hashCode) + rhsInternal.hashCode) + rhsCall.hashCode) + rhsReturn.hashCode
  val callComplete =
    (rhsCall flatMap { rhs => rhs._2 map { r => (rhs._1._1 + r._1, (rhs._1._2 + r._2)) } }).toSet
  val size = rhsInternal.size + rhsCall.size + callComplete.size
  lazy val rhs = rhsReturn.toSeq ++ rhsInternal.toSeq ++ callComplete.toSeq
}

case class RhsAttackRule[A](
    lhs: (Internal[A], Internal[A]),
    rhsReturn: Set[(Return[A], Return[A])]
  ) extends AttackRule[A] {
  override val hashCode = 31*(31 + lhs.hashCode) + rhsReturn.hashCode
  val size = rhsReturn.size
  lazy val rhs = rhsReturn.toSeq
}

object AttackRule {
  def makeReturnRule[A](
    lhs: (Internal[A], Internal[A]),
    rhsReturn: Set[(Return[A], Return[A])]
  ): AttackRule[A] = 
  makeRule(lhs, rhsReturn, Set.empty, Map.empty)

  def makeInternalRule[A](
    lhs: (Internal[A], Internal[A]),
    rhsInternal: Set[(Internal[A], Internal[A])]
  ): AttackRule[A] = 
  makeRule(lhs, Set.empty, rhsInternal, Map.empty)

  def makeCallRule[A](
    lhs: (Internal[A], Internal[A]),
    rhsCallSet: Set[(Call[A], Call[A])]
  ): AttackRule[A] = {
    var rhsCall = Map[(Internal[A], Internal[A]), Set[(Return[A], Return[A])]]()
    rhsCallSet foreach { rhs =>
      val head = (rhs._1.head, rhs._2.head)
      val tail = (rhs._1.tail, rhs._2.tail)
      rhsCall += ((head, rhsCall.getOrElse(head, Set.empty) + tail))
    }
    makeRule(lhs, Set.empty, Set.empty, rhsCall)
  }

  def makeRule[A](
      lhs: (Internal[A], Internal[A]),
      rhsReturn: Set[(Return[A], Return[A])],
      rhsInternal: Set[(Internal[A], Internal[A])],
      rhsCall: Map[(Internal[A], Internal[A]), Set[(Return[A], Return[A])]]
    ): AttackRule[A] = {
    if(rhsInternal.isEmpty && rhsCall.isEmpty) {
      RhsAttackRule[A](lhs, rhsReturn)
    }
    else {
      LhsAttackRule[A](lhs, rhsReturn, rhsInternal, rhsCall)
    }
  }
}

