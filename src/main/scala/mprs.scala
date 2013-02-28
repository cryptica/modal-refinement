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
  def toList: List[A]

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
  
  def replace(term: Process[A], replacement: Set[Process[A]])(implicit ord: Ordering[A]): Set[Process[A]] = (term, this) match {
    case (Empty(), _) => throw new IllegalArgumentException("match from empty left hand side")
    case (x, y) if x == y => replacement
    case (x +: xs, y +: ys) if x == y => ys.replace(xs, replacement)
    case (x, y +: ys) => y.replace(x, replacement) map {_ +: ys}
    case (x |: xs, y |: ys) if x == y => ys.replace(xs, replacement)
    case (x, y |: ys) => (y.replace(x, replacement) map { _ |: ys }) |
    (ys.replace(x, replacement) map { y |: _ })
    case _ => Set(this)
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
  override def toList = Nil
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
  override def toList = List(id)
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
  override def length = 1 + tail.length
  override def isEmpty = false
  override def apply(idx: Int) = if(idx == 0) head else tail(idx - 1)
  override def toList = head.toList ::: tail.toList
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

case class RewriteRule[A](
  val ruleType: RuleType,
  val lhs: Process[A],
  val action: String,
  val rhs: Process[A]) {
  require(lhs != Empty[A]())

  override def toString = lhs.toString + " " + action + ruleType + " " + rhs.toString

  def apply(p: Process[A])(implicit ord: Ordering[A]): Set[Process[A]] = {
    p.replace(lhs, Set(rhs))
  }
}
sealed abstract class RuleType
case object MayRule extends RuleType {
  override val toString = "?"
}
case object MustRule extends RuleType {
  override val toString = "!"
}

/**
 * The class MPRS represents a modal process rewrite system given
 * by an inital process and a set of rewrite rules.
 */
class MPRS[A](val initialLHS: Process[A], val initialRHS: Process[A],
  val rules: Set[RewriteRule[A]])(implicit ord: Ordering[A]) {
  
  val actions = (rules map { _.action })
  val constants = ((initialLHS.constants | initialRHS.constants) /: rules)
    { (set, rule) => set | rule.lhs.constants | rule.rhs.constants }

  override def toString = "InitialLHS: " + initialLHS + "\n" +
      "InitialRHS: " + initialRHS + "\n" + rules.mkString("\n")
  
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
        case RewriteRule(_, _ +: Const(_), a, Const(_)) => (a, 0)
        case RewriteRule(_, _ +: Const(_), a, _ +: Const(_)) => (a, 1)
        case RewriteRule(_, _ +: Const(_), a, _ +: _ +: Const(_)) => (a, 2)
        case _ => ("", -1)
      }
      arity >= 0 && (arities.put(action, arity) forall { _ == arity })
    }
  }
}
