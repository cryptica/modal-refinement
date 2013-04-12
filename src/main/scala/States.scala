abstract sealed class VPDAProcess[A]
case class Return[A](s1: A) extends VPDAProcess[A] {
  def +(that: Return[A]): Internal[A] = Internal(s1, that.s1)
  override def toString = s1.toString
}
case class Internal[A](s1: A, s2: A) extends VPDAProcess[A] {
  def +(that: Return[A]): Call[A] = Call(s1, s2, that.s1)
  override def toString = s1 + "." + s2
}
case class Call[A](s1: A, s2: A, s3: A) extends VPDAProcess[A] {
  def head = Internal(s1, s2)
  def tail = Return(s3)
  override def toString = s1 + "." + s2 + "." + s3
}

abstract sealed class State[A] {
  type S <: VPDAProcess[A]
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
  def +(that: ReturnState[A]): CallState[A] =
    CallState(left + that.left, right + that.right)
}
case class CallState[A](left: Call[A], right: Call[A]) extends State[A] {
  type S = Call[A]
  def head = InternalState(left.head, right.head)
  def tail = ReturnState(left.tail, right.tail)
}

