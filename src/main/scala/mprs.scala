import scala.collection.immutable.LinearSeq

/**
 * The class Process represents a process term given by
 *  P ::= ε
 *      | X
 *      | t_1. … .t_n
 *      | t_1 || … || t_n
 * where ε denotes the empty process, X the constant process and
 * t_1 to t_n are process terms.
**/
sealed abstract class Process extends LinearSeq[Process] {
  def constants: Set[String]
  def size: Int
  //def isEmpty: Boolean
  //def head: Process
  //def tail: Process
}
case object Empty extends Process {
  override def toString = "ε"
  override def size = 0
  override def length = 0
  override def isEmpty = true
  override def constants = Set.empty
  override def head = throw new UnsupportedOperationException("head of empty process")
  override def tail = throw new UnsupportedOperationException("tail of empty process")
  override def apply(idx: Int) = throw new IndexOutOfBoundsException(idx.toString)
}
case class Constant(id: String) extends Process {
  override def toString = id
  override def size = 1
  override def length = 1
  override def isEmpty = false
  override def constants = Set(id)
  override def head = this
  override def tail = Empty
  override def apply(idx: Int) = if(idx == 0) this else throw new IndexOutOfBoundsException(idx.toString)
}
case class Parallel(children: Seq[Process]) extends ComposedProcess {
  override def toString = children.mkString("(", "|", ")")
  val isParallel = true
}
case class Sequential(children: Seq[Process]) extends ComposedProcess{
  override def toString = children.mkString(".")
  val isParallel = false
}
sealed abstract trait ComposedProcess extends Process {
  val children: Seq[Process]
  val isParallel: Boolean
  override def size = (children :\ 0) {_.size + _}
  override def length = children.length
  override def isEmpty = false
  override def constants = (Set.empty[String] /: children) {_ | _.constants}
  override def head = children.head
  override def tail = Process.makeComposed(isParallel, children.tail)
  override def apply(idx: Int) = children(idx)
}

object Process {
  object ProcessOrdering extends Ordering[Process] {
    private def compareChildren(childrenA: Seq[Process], childrenB: Seq[Process]): Int = {
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

  def makeComposed(isParallel: Boolean, children: Seq[Process]): Process = {
    val flatChildren = (children map { _ match {
      case Parallel(children) if isParallel => children
      case Sequential(children) if !isParallel => children
      case Empty => List()
      case process => List(process)
    }}).flatten
    if(flatChildren.isEmpty) {
      Empty
    }
    else if(flatChildren.length == 1) {
      flatChildren.head
    }
    else if(isParallel) {
      Parallel(flatChildren.sorted)
    }
    else {
      Sequential(flatChildren)
    }
  }
  
  def makeEmpty = Empty
  def makeConstant(id: String) = Constant(id)
  def makeParallel(children: Seq[Process]) = makeComposed(true, children)
  def makeSequential(children: Seq[Process]) = makeComposed(false, children)

  def applyRule(rule: RewriteRule): List[Process] = List()
}

sealed abstract case class RewriteRule(lhs: Process, action: String, rhs: Process) {
  protected val ruleTypeString: String
  override def toString = lhs.toString + " " + action + ruleTypeString + " " + rhs.toString
}
class MayRule(lhs: Process, action: String, rhs: Process)
    extends RewriteRule(lhs, action, rhs) {
  override val ruleTypeString = "?"
}
class MustRule(lhs: Process, action: String, rhs: Process)
  extends RewriteRule(lhs, action, rhs) {
  override val ruleTypeString = "!"
}

/**
 * The class MPRS represents a modal process rewrite system given
 * by an inital process and a set of rewrite rules.
**/
case class MPRS(initial: Process, rules: Seq[RewriteRule]) {
  
  val actions = Set(rules map { _.action })
  val constants = (initial.constants /: rules) { (set, rule) =>
      set | rule.lhs.constants | rule.rhs.constants }

  override def toString = "Initial: " + initial + "\n" + rules.mkString("\n")
  
  def asVPDA() = {
    rules foreach { rule =>
      val lhs = rule.lhs
      val rhs = rule.rhs
      println(lhs.head + " -> " + rhs.head + " (" + rule.action
        + ";" + lhs.tail + "/" + rhs.tail + ")")
    }
  }

  def isVPDA = {
    val arity = new scala.collection.mutable.HashMap[String, Int]()
    initial.length ==2 && (
    rules forall { rule =>
      val rhsSize = rule.rhs.size
      rule.lhs.isInstanceOf[Sequential] &&
      rule.lhs.size == 2 &&
      (arity.put(rule.action, rhsSize) match {
        case None => rhsSize >= 1 && rhsSize <= 3
        case Some(oldSize) => oldSize == rhsSize
      }) &&
      (rule.rhs.isInstanceOf[Constant] || (rule.rhs.isInstanceOf[Sequential] &&
        rule.rhs.length == rhsSize))
    })
  }
}
