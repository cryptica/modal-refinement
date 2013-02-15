/**
 * The class Process represents a process term given by
 *  P ::= ε
 *      | X
 *      | t_1. … .t_n
 *      | t_1 |: … |: t_n
 * where ε denotes the empty process, X the constant process and
 * t_1 to t_n are process terms.
**/
sealed abstract class Process[A] {
  def constants: Set[A]
  def size: Int
  def length: Int
  def isEmpty: Boolean
  def head: Process[A]
  def tail: Process[A]
  def apply(idx: Int): Process[A]

  def +:(p: Process[A]): Process[A] = {
    (p, this) match {
      case (Empty(), _) => this
      case (_, Empty()) => p
      case (head +: tail, _) => new +:(head, tail +: this)
      case _ => new +:(p, this)
    }
  }

  def |:(p: Process[A])(implicit ord: Ordering[Process[A]]): Process[A] =
    (p, this) match {
      case (Empty(), _) => this
      case (_, Empty()) => p
      case (head |: tail, _) =>
        new |:(head, tail |: this)
      case (_, head |: tail) => if (ord.compare(p, head) > 0)
        new |:(head, p |: tail) else new |:(p, this)
      case _ => if(ord.compare(p, this) > 0)
        new |:(this, p) else new |:(p, this)
    }

  def zip[B](p: Process[B])(implicit ordA: Ordering[A], ordB: Ordering[B]): Process[(A,B)] = (this, p) match {
    case (Empty(), Empty()) => Empty()
    case (Empty(), _) | (Empty(), _) => throw new IllegalArgumentException("processes of unequal length")
    case (Const(x), Const(y)) => Const((x, y))
    case (x +: xs, y +: ys) => (x zip y) +: (xs zip ys)
    case (x |: xs, y |: ys) => (x zip y) |: (xs zip ys)
    case _ => throw new IllegalArgumentException("processes of unequal type")
  }
}

case class Empty[A]() extends Process[A] {
  override def toString = "ε"
  override def size = 0
  override def length = 0
  override def isEmpty = true
  override def constants = Set.empty[A]
  override def head = throw new UnsupportedOperationException("head of empty process")
  override def tail = throw new UnsupportedOperationException("tail of empty process")
  override def apply(idx: Int) = throw new IndexOutOfBoundsException(idx.toString)
}
case class Const[A](id: A) extends Process[A] {
  override def toString = id.toString
  override def size = 1
  override def length = 1
  override def isEmpty = false
  override def constants = Set(id)
  override def head = this
  override def tail = Empty()
  override def apply(idx: Int) = if(idx == 0) this else throw new IndexOutOfBoundsException(idx.toString)
}
case class |:[A](override val head: Process[A], override val tail: Process[A]) extends ComposedProcess[A] {
  override def toString = "(" + head.toString + "|" + tail.toString + ")"
  override def constants = head.constants | tail.constants
}
case class +:[A](override val head: Process[A], override val tail: Process[A]) extends ComposedProcess[A] {
  override def toString = "(" + head.toString + "." + tail.toString + ")"
  override def constants = head.constants | tail.constants
}
sealed abstract trait ComposedProcess[A] extends Process[A] {
  override def size = head.size + tail.size + 1
  override def length = 1 + tail.size
  override def isEmpty = false
  override def apply(idx: Int) = if(idx == 0) head else tail(idx - 1)
}

class ProcessOrdering[A](ord: Ordering[A]) extends Ordering[Process[A]] {
  def compare(a: Process[A], b: Process[A]) = (a, b) match {
    case (Const(x), Const(y)) => ord.compare(x, y)
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
  implicit def processOrdering[A](implicit ord: Ordering[A]): Ordering[Process[A]] = new ProcessOrdering(ord)

  def makeEmpty[A] = new Empty[A]()
  def makeConst[A](const: A) = Const(const)
  def makeParallel[A](children: List[Process[A]])(implicit ord: Ordering[A]): Process[A] = children match {
    case Nil => Empty()
    case head :: tail => head |: makeParallel(tail)
  }
  def makeSequential[A](children: List[Process[A]]): Process[A] = children match {
    case Nil => Empty()
    case head :: tail => head +: makeSequential(tail)
  }
}

sealed abstract class RewriteRule[A] {

  val lhs: Process[A]
  val action: String
  val rhs: Process[A]
  require(lhs != Empty[A]())

  protected val ruleTypeString: String
  override def toString = lhs.toString + " " + action + ruleTypeString + " " + rhs.toString

  private def findMatch(term: Process[A], process: Process[A])(implicit ord: Ordering[A]): Option[Process[A]] = (term, process) match {
    case (Empty(), _) => throw new IllegalArgumentException("match from empty left hand side")
    case (x, y) if x == y => Some(rhs)
    case (x +: xs, y +: ys) if x == y => findMatch(xs, ys)
    case (x, y +: ys) => findMatch(x, y) map {_ +: ys}
    case (x |: xs, y |: ys) if x == y => findMatch(xs, ys)
    case (x, y |: ys) => (findMatch(x, y) map { _ |: ys }) orElse
    (findMatch(x, ys) map { y |: _ })
    case _ => None
  }
  def apply(p: Process[A])(implicit ord: Ordering[A]): Option[Process[A]] = {
    findMatch(lhs, p)
  }
}
object RewriteRule {
  def unapply[A](rule : RewriteRule[A]) : Some[(Process[A], String, Process[A])] =
    Some((rule.lhs, rule.action, rule.rhs))
}
case class MayRule[A](override val lhs: Process[A], override val action: String, override val rhs: Process[A])
    extends RewriteRule[A] {
  override val ruleTypeString = "?"
}
case class MustRule[A](override val lhs: Process[A], override val action: String, override val rhs: Process[A])
  extends RewriteRule[A] {
  override val ruleTypeString = "!"
}

/**
 * The class MPRS represents a modal process rewrite system given
 * by an inital process and a set of rewrite rules.
 */
class MPRS[A](val initial: Process[A], val rules: Seq[RewriteRule[A]])(implicit ord: Ordering[A]) {
  
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
      val (action, arity) = (rule.lhs, rule.action, rule.rhs) match {
        case (_ +: Const(_), a, Const(_)) => (a, 0)
        case (_ +: Const(_), a, _ +: Const(_)) => (a, 1)
        case (_ +: Const(_), a, _ +: _ +: Const(_)) => (a, 2)
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
