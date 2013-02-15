import scala.collection.immutable.LinearSeq

/**
 * The class Process represents a process term given by
 *  P ::= ε
 *      | X
 *      | t_1. … .t_n
 *      | t_1 |: … |: t_n
 * where ε denotes the empty process, X the constant process and
 * t_1 to t_n are process terms.
**/
sealed abstract class Process {
  def constants: Set[String]
  def size: Int
  def isEmpty: Boolean
  def head: Process
  def tail: Process
  def apply(idx: Int): Process

  def +:(p: Process): Process = {
    (p, this) match {
      case (Empty, _) => this
      case (_, Empty) => p
      case (head +: tail, _) => new +:(head, tail +: this)
      case _ => new +:(p, this)
    }
  }
  def |:(p: Process): Process = {
    (p, this) match {
      case (Empty, _) => this
      case (_, Empty) => p
      case (head |: tail, _) =>
        new |:(head, tail |: this)
      case (_, head |: tail) => if (ProcessOrdering.compare(p, head) > 0)
        new |:(head, p |: tail) else new |:(p, this)
      case _ => if(ProcessOrdering.compare(p, this) > 0)
        new |:(this, p) else new |:(p, this)
    }
  }
}
case object Empty extends Process {
  override def toString = "ε"
  override def size = 0
  override def isEmpty = true
  override def constants = Set.empty
  override def head = throw new UnsupportedOperationException("head of empty process")
  override def tail = throw new UnsupportedOperationException("tail of empty process")
  override def apply(idx: Int) = throw new IndexOutOfBoundsException(idx.toString)
}
case class Const(id: String) extends Process {
  override def toString = id
  override def size = 1
  override def isEmpty = false
  override def constants = Set(id)
  override def head = this
  override def tail = Empty
  override def apply(idx: Int) = if(idx == 0) this else throw new IndexOutOfBoundsException(idx.toString)
}
case class |:(override val head: Process, override val tail: Process) extends ComposedProcess{
  override def toString = "(" + head.toString + "|" + tail.toString + ")"
}
case class +:(override val head: Process, override val tail: Process) extends ComposedProcess{
  override def toString = "(" + head.toString + "." + tail.toString + ")"
}
sealed abstract trait ComposedProcess extends Process {
  override def size = head.size + tail.size + 1
  override def isEmpty = false
  override def constants = head.constants | tail.constants
  override def apply(idx: Int) = if(idx == 0) head else tail(idx - 1)
}

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
    case (Const(idA), Const(idB)) => idA.compare(idB)
    case (head1 |: tail1, head2 |: tail2) =>
      val c = compare(head1, head2)
      if(c != 0) c else compare(tail1, tail2)
    case (head1 +: tail1, head2 +: tail2) =>
      val c = compare(head1, head2)
      if(c != 0) c else compare(tail1, tail2)
    case _ => a.getClass.toString.compare(b.getClass.toString)
  }
}

object Process {
  implicit def processOrdering: Ordering[Process] = ProcessOrdering
  
  def makeEmpty = Empty
  def makeConst(id: String) = Const(id)
  def makeParallel(children: List[Process]): Process = children match {
    case Nil => Empty
    case head :: tail => head |: makeParallel(tail)
  }
  def makeSequential(children: List[Process]): Process = children match {
    case Nil => Empty
    case head :: tail => head +: makeSequential(tail)
  }

  def applyRule(rule: RewriteRule): List[Process] = List()
}

sealed abstract case class RewriteRule(lhs: Process, action: String, rhs: Process) {
  require(lhs != Empty)

  protected val ruleTypeString: String
  override def toString = lhs.toString + " " + action + ruleTypeString + " " + rhs.toString

  private def findMatch(term: Process, process: Process): Option[Process] = {
    (term, process) match {
      case (Empty, _) => throw new IllegalArgumentException("match from empty left hand side")
      case (x, y) if x == y => Some(rhs)
      case (x +: xs, y +: ys) if x == y => findMatch(xs, ys)
      case (x, y +: ys) => findMatch(x, y) map {_ +: ys}
      case (x |: xs, y |: ys) if x == y => findMatch(xs, ys)
      case (x, y |: ys) => (findMatch(x, y) map { _ |: ys }) orElse
      (findMatch(x, ys) map { y |: _ })
      case _ => None
    }
  }
  def apply(p: Process): Option[Process] = {
    findMatch(lhs, p)
  }
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
  
  val actions = rules map { _.action }
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
    val arities = new scala.collection.mutable.HashMap[String, Int]()
    rules forall { rule => 
      val (action, arity) = rule match {
        case RewriteRule(_ +: Const(_), a, Const(_)) => (a, 0)
        case RewriteRule(_ +: Const(_), a, _ +: Const(_)) => (a, 1)
        case RewriteRule(_ +: Const(_), a, _ +: _ +: Const(_)) => (a, 2)
        case _ => ("", -1)
      }
      arity >= 0 && (arities.put(action, arity) forall { _ == arity })
    }
  }

  def applyRules() {
    val worklist = scala.collection.mutable.Queue(initial)
    val states = scala.collection.mutable.HashSet(initial)
    var i = 0
    while(worklist.nonEmpty && i < 20) {
      i += 1
      val state = worklist.dequeue()
      states += state
      for {rule <- rules} {
        val result = rule(state)
        result match {
          case Some(res) if !states.contains(res) =>
            println("Rule " + rule + " applied to " + state + " yields " + res)
            worklist += res
            states += res
          case _ =>
        }
      }
    }
  }
}
