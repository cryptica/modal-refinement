
class MVPDA[A](
  val returnRules: Map[(String, RuleType), Map[Internal[A], Set[Return[A]]]],
  val internalRules: Map[(String, RuleType), Map[Internal[A], Set[Internal[A]]]],
  val callRules: Map[(String, RuleType), Map[Internal[A], Set[Call[A]]]]
)

object MVPDA {

  private def error(msg: String) =
    throw new IllegalArgumentException("Given mPRS is not an mvPDA: " + msg)

  def makeInitial[A](p: Process[A], q: Process[A]) = (p, q) match {
    case (Const(p1) +: Const(p2), Const(q1) +: Const(q2)) =>
      InternalState[A](Internal(p1, p2), Internal(q1, q2))
    case _ => error("inital state invalid: " + p + " ≤ " + q)
  }

  /**
   * Test if the given modal process rewrite system is
   * a visible PDA. An mPRS is a vPDA if the actions can
   * be partitioned into three sets for internal, call or
   * return actions.
   * @param mprs the mPRS to be tested
   * @return true if the mPRS is a vPDA, otherwise false
   */ 
  def makeMVPDA[A](mprs: MPRS[A]): MVPDA[A] = {

    var returnRules = Map[(String, RuleType), Map[Internal[A], Set[Return[A]]]]()
    var internalRules = Map[(String, RuleType), Map[Internal[A], Set[Internal[A]]]]()
    var callRules = Map[(String, RuleType), Map[Internal[A], Set[Call[A]]]]()

    mprs.rules foreach { rule =>
      rule match {
        case RewriteRule(rt, Const(l1) +: Const(l2), action, r) =>
          val lhs = Internal(l1, l2)
          def updateRules[B](
            ruleMap: Map[(String, RuleType), Map[Internal[A], Set[B]]],
            rhs: B
          ) = {
            val curRules = ruleMap.getOrElse((action, rt), Map.empty)
            val curSet = curRules.getOrElse(lhs, Set.empty)
            ruleMap + (((action, rt), curRules + ((lhs, curSet + rhs))))
          }
          r match {
            case Const(r1) =>
              returnRules = updateRules(returnRules, Return(r1))
            case Const(r1) +: Const(r2) => 
              internalRules = updateRules(internalRules, Internal(r1, r2))
            case Const(r1) +: Const(r2) +: Const(r3) =>
              callRules = updateRules(callRules, Call(r1, r2, r3))
            case _ => error("right-hand side of rewrite rule invalid: " + rule)
          }
        case _ => error("left-hand side of rewrite rule invalid: " + rule)
      }
    }
    val a1 = returnRules.keySet map { _._1 }
    val a2 = internalRules.keySet map { _._1 }
    val a3 = callRules.keySet map { _._1 }
    if((a1 & a2).nonEmpty || (a2 & a3).nonEmpty || (a3 & a1).nonEmpty) {
      error("action set can not be partitioned")
    }
    new MVPDA(returnRules, internalRules, callRules)
  }
}

