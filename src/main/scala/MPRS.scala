/**
 * A RewriteRule object represents a rewrite rule in an mPRS
 * given by the rule type, the left-hand side process,
 * the action and the right-hand side process.
 * The left-hand side must not be empty.
 * The rule type is either may rule or must rule.
 */
case class RewriteRule[A](
  val ruleType: RuleType,
  val lhs: Process[A],
  val action: String,
  val rhs: Process[A]) {
  require(lhs != Empty[A]())

  override def toString = lhs.toString + " " + action + ruleType + " " + rhs.toString
}
sealed abstract class RuleType
case object MayRule extends RuleType {
  override val toString = "?"
}
case object MustRule extends RuleType {
  override val toString = "!"
}

/**
 * An MPRS object represents a modal process rewrite system
 * given by a set of rewrite rules.
 */
case class MPRS[A](val rules: Set[RewriteRule[A]]) {
  override def toString = rules.mkString("\n")
}
