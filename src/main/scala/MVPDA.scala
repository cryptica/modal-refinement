
abstract sealed class MVPDAState[A]
case class Return[A](s: A) extends MVPDAState[A] {
  def +(ret: Return[A]): Internal[A] = Internal((s, ret.s))
  override def toString = s.toString
}
case class Internal[A](s: (A, A)) extends MVPDAState[A] {
  def +(ret: Return[A]): Call[A] = Call((s, ret.s))
  override def toString = s.toString
}
case class Call[A](s: ((A, A), A)) extends MVPDAState[A] {
  def head = Internal(s._1)
  def tail = Return(s._2)
  override def toString = s.toString
}

class MVPDA[A](
  val initial: State[A, Internal[A]],
  val returnRules: Map[(String, RuleType), Map[Internal[A], Set[Return[A]]]],
  val internalRules: Map[(String, RuleType), Map[Internal[A], Set[Internal[A]]]],
  val callRules: Map[(String, RuleType), Map[Internal[A], Set[Call[A]]]]
)

object MVPDA {

  /**
   * Test if the given modal process rewrite system is
   * a visible PDA. An mPRS is a vPDA if the actions can
   * be partitioned into three sets for internal, call or
   * return actions.
   * @param mprs the mPRS to be tested
   * @return true if the mPRS is a vPDA, otherwise false
   */ 
  def makeMVPDA[A](mprs: MPRS[A]): MVPDA[A] = {
    val initial = {
      (mprs.initialLeft, mprs.initialRight) match {
        case (Const(p1) +: Const(p2), Const(q1) +: Const(q2)) =>
          State[A, Internal[A]](Internal((p1, p2)), Internal((q1, q2)))
        case _ =>
          throw new IllegalArgumentException("Given mPRS is not an mvPDA")
      }
    }
    var returnRules = Map[(String, RuleType), Map[Internal[A], Set[Return[A]]]]()
    var internalRules = Map[(String, RuleType), Map[Internal[A], Set[Internal[A]]]]()
    var callRules = Map[(String, RuleType), Map[Internal[A], Set[Call[A]]]]()
    mprs.rules foreach { rule => rule match {
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1)) =>
        val lhs = Internal((l1, l2))
        val curRules = returnRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse(lhs, Set.empty)
        returnRules += (((a, rt), curRules + ((lhs, curSet + Return(r1)))))
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1) +: Const(r2)) =>
        val lhs = Internal((l1, l2))
        val curRules = internalRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse(lhs, Set.empty)
        internalRules += (((a, rt), curRules + ((lhs, curSet + Internal((r1, r2))))))
      case RewriteRule(rt, Const(l1) +: Const(l2), a, Const(r1) +: Const(r2) +: Const(r3)) =>
        val lhs = Internal((l1, l2))
        val curRules = callRules.getOrElse((a, rt), Map.empty)
        val curSet = curRules.getOrElse(lhs, Set.empty)
        callRules += (((a, rt), curRules + ((lhs, curSet + Call(((r1, r2), r3))))))
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
    new MVPDA(initial, returnRules, internalRules, callRules)
  }
}
