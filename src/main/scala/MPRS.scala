
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
 * The class MPRS represents a modal process rewrite system.
 */
class MPRS[A](val rules: Set[RewriteRule[A]])(implicit ord: Ordering[A]) {
  override def toString = rules.mkString("\n")
}
