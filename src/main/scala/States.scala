/**
 * The classes in this file are provided to capsule information on
 * processes of vPDAs and states appearing in attack rules and
 * provide some functions to combine and dissect them.
 */

/**
 * VPDAProcess object represent the processes appearing in rewrite
 * rules of an vPDA. They correspond to the processes appearing on
 * the right-hand side of return, internal and call rules, respectively.
 */
abstract sealed class VPDAProcess[A]
case class Return[A](s1: A) extends VPDAProcess[A] {
  /**
   * Concatenate this return process P with that return proess S
   * and return an new internal process P⋅S.
   */
  def +(that: Return[A]): Internal[A] = Internal(s1, that.s1)
  override def toString = s1.toString
}
case class Internal[A](s1: A, s2: A) extends VPDAProcess[A] {
  /**
   * Concatenate this internal process P⋅S with that return proess S'
   * and return an new call process P⋅S⋅S'.
   */
  def +(that: Return[A]): Call[A] = Call(s1, s2, that.s1)
  override def toString = s1 + "." + s2
}
case class Call[A](s1: A, s2: A, s3: A) extends VPDAProcess[A] {
  /**
   * For this call process P⋅S⋅S', return the head internal process P⋅S.
   */
  def head = Internal(s1, s2)
  /**
   * For this call process P⋅S⋅S', return the tail return process S'.
   */
  def tail = Return(s3)
  override def toString = s1 + "." + s2 + "." + s3
}

/**
 * State objects represent a paired state (p,q) for
 * two vPDA processes p and q.
 * The subclasses ReturnState, InternalState and
 * CallState correspond to the process classes
 * Return, Internal and Call.
 */
abstract sealed class State[A] {
  type S <: VPDAProcess[A]
  val left: S
  val right: S
  override def toString = "(" + left + "," + right + ")"
}
case class ReturnState[A](left: Return[A], right: Return[A]) extends State[A] {
  type S = Return[A]
  /**
   * Concatenate this return state (P,Q) with that return state (S,T) and return an new
   * internal state (P⋅S,Q⋅T).
   */
  def +(that: ReturnState[A]): InternalState[A] =
    InternalState(left + that.left, right + that.right)
}
case class InternalState[A](left: Internal[A], right: Internal[A]) extends State[A] {
  type S = Internal[A]

  /**
   * Concatenate this internal state (P⋅S,Q⋅T) with that return state (S',T')
   * and return a new call state (P⋅S⋅S',Q⋅T⋅T').
   */
  def +(that: ReturnState[A]): CallState[A] =
    CallState(left + that.left, right + that.right)
}
case class CallState[A](left: Call[A], right: Call[A]) extends State[A] {
  type S = Call[A]
  /**
   * For this call state (P⋅S⋅S',Q⋅T⋅T'), return the head internal state
   * (P⋅S,Q⋅T).
   */
  def head = InternalState(left.head, right.head)
  /**
   * For this call state (P⋅S⋅S',Q⋅T⋅T'), return the tail return state
   * (S',T').
   */
  def tail = ReturnState(left.tail, right.tail)
}

