
/**
 * The class Process represents a process term given by
 *  P ::= ε
 *      | X
 *      | t_1. … .t_n
 *      | t_1 || … || t_n
 * where ε denotes the empty process, X the constant process and
 * t_1 to t_n are process terms.
**/
sealed abstract class Process
case object Empty extends Process {
  override def toString() = "ε"
}
case class Constant(id: String) extends Process {
  override def toString() = id
}
case class Parallel(children: Seq[Process]) extends Process {
  override def toString() = children.mkString("(", "|", ")")
}
case class Sequential(children: Seq[Process]) extends Process {
  override def toString() = children.mkString(".")
}

object Process {

  object ProcessOrdering extends Ordering[Process] {
    private def compareChildren( childrenA: Seq[Process], childrenB: Seq[Process]): Int = {
      val ae = childrenA.iterator
      val be = childrenB.iterator
      while(ae.hasNext && be.hasNext) {
        val res = ProcessOrdering.compare(ae.next, be.next)
        if(res != 0) return res
      }
      Ordering.Boolean.compare(ae.hasNext, be.hasNext)
    }

    def compare(a: Process, b: Process) = (a, b) match {
      case (Constant(idA), Constant(idB)) => idA.compare(idB)
      case (Parallel(childrenA), Parallel(childrenB)) =>
        compareChildren(childrenA, childrenB)
      case (Sequential(childrenA), Sequential(childrenB)) =>
        compareChildren(childrenA, childrenB)
      case _ => a.getClass.toString.compare(b.getClass.toString)
    }
  }
  implicit def processOrdering: Ordering[Process] = ProcessOrdering

  def toNormalForm(p: Process): Process = {
    def flattenChildren(isParallel: Boolean, children: Seq[Process]) = {
      val flatChildren = (children map toNormalForm map { _ match {
        case Parallel(children) if isParallel => children
        case Sequential(children) if !isParallel => children
        case Empty => List()
        case process => List(process)
      }}).flatten
      if(flatChildren.isEmpty) {
        Empty
      }
      else if(flatChildren.size == 1) {
        flatChildren.head
      }
      else if(isParallel) {
        new Parallel(flatChildren.sorted)
      }
      else {
        new Sequential(flatChildren)
      }
    }
    p match {
      case Empty | Constant(_)=> p
      case Parallel(children) =>
        flattenChildren(true, children)
      case Sequential(children) =>
        flattenChildren(false, children)
    }
  }

  def applyRule(rule: RewriteRule): List[Process] = List()
}

sealed abstract class RewriteRule(lhs: Process, action: String, rhs: Process) {
  val ruleType: String
  override def toString() = lhs.toString + " " + action + ruleType + " " + rhs.toString
}
case class MayRule(lhs: Process, action: String, rhs: Process)
    extends RewriteRule(lhs, action, rhs) {
  override val ruleType = "?"
}
case class MustRule(lhs: Process, action: String, rhs: Process)
  extends RewriteRule(lhs, action, rhs) {
  override val ruleType = "!"
}

/**
 * The class MPRS represents a modal process rewrite system given
 * by an inital process and a set of rewrite rules.
**/
case class MPRS(initial: Process, rules: Seq[RewriteRule]) {
  override def toString() = "Initial: " + initial + "\n" + rules.mkString("\n")
}

