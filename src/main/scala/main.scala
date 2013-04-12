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

  def fromAST(ast: CommonTree): MPRS[String] = {
    val token = ast.getToken
    val tokenType = token.getType
    if(tokenType == xMPRSParser.MPRS) {
      val children = getChildren(ast)
      val initialLeft = makeProcess(children(0))
      val initialRight = makeProcess(children(1))
      val rules = (children.drop(2) map { makeRule(_) }).flatten
      new MPRS(initialLeft, initialRight, rules.toSet)
    }
    else {
      throw new IllegalTokenException("Expected an mPRS, got " + tokenType)
    }
  }
}

object Main extends App {

  private def treeToSeq(ast: CommonTree): List[String] = {
    val buffer = new ListBuffer[String]()
    val token = ast.getToken
    buffer += token.getText
    val children = ast.getChildren
    val childlist = if(children != null) {
      buffer += "("
      children.asScala map { child => 
        val tree = child.asInstanceOf[CommonTree]
        buffer ++= treeToSeq(tree)
      }
      buffer += ")"
    }
    buffer.toList
  }

  def testFileForRefinement(file: File) = {
    val input = new FileInputStream(file)
    val lexer = new xMPRSLexer(new ANTLRInputStream((input)))
    val tokens = new CommonTokenStream(lexer)
    val parser = new xMPRSParser(tokens)
    val mprsTree = parser.mprs
    input.close()
    val result = mprsTree.tree.asInstanceOf[CommonTree];
    val mprs = MPRSParser.fromAST(result)
    val mvpda = MVPDA.makeMVPDA(mprs)
    //println(mprs)
    val tester = new RefinementTester(mvpda)
    tester.testRefinement()
  }

  for(filename <- args) {
    try {
      val file = new File(filename)
      val t0 = System.nanoTime()
      val result = testFileForRefinement(file)
      val t1 = System.nanoTime()
      val code = if(result) "1" else "0"
      val time = (t1 - t0) * 1e-09
      println("[" + code + "] " + filename + " (" + time + " s)")
    }
    catch {
      // possible exceptions: IllegalArgumentException, IllegalTokenException, IOException
      case e: Exception =>
        println("[E] " + filename + " (" + e + ")")
    }
  }
}

