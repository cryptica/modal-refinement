import org.antlr.runtime._
import org.antlr.runtime.tree.CommonTree;

import java.io.IOException
import java.io.File
import java.io.FileInputStream
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer

class IllegalTokenException(message: String, cause: Throwable)
    extends RuntimeException(message, cause) {
  def this(message: String) = this(message, null)
  def this(cause: Throwable) = this(cause.toString, cause)
}

object MPRSParser {
  private def getChildren(ast: CommonTree) = {
    (ast.getChildren.asScala map { _.asInstanceOf[CommonTree] }).toList
  }
  private def makeAction(ast: CommonTree): String = {
    val token = ast.getToken
    val tokenType = token.getType
    tokenType match {
      case xMPRSParser.ACTION => token.getText
      case _ => throw new IllegalTokenException("Expected an action, got " + tokenType)
    }
  }
  private def makeRule(ast: CommonTree): List[RewriteRule[String]] = {
    val token = ast.getToken
    val tokenType = token.getType
    tokenType match {
      case xMPRSParser.MAY_RULE | xMPRSParser.MUST_RULE =>
        val children = getChildren(ast)
        val lhs = makeProcess(children(0))
        val action = makeAction(children(1))
        val rhs = makeProcess(children(2))
        tokenType match {
          case xMPRSParser.MAY_RULE =>
            List(new RewriteRule(MayRule, lhs, action, rhs))
          case xMPRSParser.MUST_RULE =>
            List(new RewriteRule(MayRule, lhs, action, rhs),
                 new RewriteRule(MustRule, lhs, action, rhs))
        }
      case _ => throw new IllegalTokenException("Expected a rule type, got " + tokenType)
    }
  }
  private def makeProcess(ast: CommonTree): Process[String] = {
    val token = ast.getToken
    val tokenType = token.getType
    def getChildrenProcess() = getChildren(ast) map { makeProcess(_) }
    tokenType match {
      case xMPRSParser.EMPTY => Process.makeEmpty
      case xMPRSParser.CONSTANT => Process.makeConst(token.getText)
      case xMPRSParser.PARALLEL => Process.makeParallel(getChildrenProcess)
      case xMPRSParser.SEQUENTIAL => Process.makeSequential(getChildrenProcess)
      case _ => throw new IllegalTokenException("Expected a process, got " + tokenType)
    }
  }

  def fromAST(ast: CommonTree) = {
    val token = ast.getToken
    val tokenType = token.getType
    if(tokenType == xMPRSParser.MPRS) {
      val children = getChildren(ast)
      val p = makeProcess(children(0))
      val q = makeProcess(children(1))
      val rules = (children.drop(2) map { makeRule(_) }).flatten
      val mprs = new MPRS(rules.toSet)
      (p, q, mprs)
    }
    else {
      throw new IllegalTokenException("Expected an mPRS, got " + tokenType)
    }
  }
}

object Main extends App {

  def testFileForRefinement(file: File, verbose: Boolean) = {
    val input = new FileInputStream(file)
    val lexer = new xMPRSLexer(new ANTLRInputStream((input)))
    val tokens = new CommonTokenStream(lexer)
    val parser = new xMPRSParser(tokens)
    val mprsTree = parser.mprs
    input.close()
    val result = mprsTree.tree.asInstanceOf[CommonTree];
    val (p, q, mprs) = MPRSParser.fromAST(result)
    val initial = MVPDA.makeInitial(p, q)
    val mvpda = MVPDA.makeMVPDA(mprs)
    //println(mprs)
    val tester = new RefinementTester(mvpda)
    tester.testRefinement(initial, verbose)
  }
  
  val verbose = args.contains("-v")
  val filenames = args.filter(_ != "-v")


// TODO remove i
  for { filename <- filenames; i <- 1 to 50 } {
    try {
      val file = new File(filename + i)
      val t0 = System.nanoTime()
      val (numRules, result) = testFileForRefinement(file, verbose)
      val t1 = System.nanoTime()
      val code = if(result) "1" else "0"
      val time = (t1 - t0) * 1e-09
      //println("[" + code + "] " + filename + " (" + "%.3f".format(time) + " s)")
      println(code + " " + i + ".0 " + time + " " + numRules)
    }
    catch {
      // possible exceptions: IllegalArgumentException, IllegalTokenException, IOException
      case e: Exception =>
        println("[E] " + filename + " (" + e + ")")
    }
  }
}

