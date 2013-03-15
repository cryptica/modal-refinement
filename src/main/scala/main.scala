import org.antlr.runtime._
import org.antlr.runtime.tree.CommonTree;
import java.io.IOException
import java.io.File
import java.io.FileInputStream
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer

case class IllegalTokenException(errorMsg: String) extends RuntimeException(errorMsg)

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
      val initialLHS = makeProcess(children(0))
      val initialRHS = makeProcess(children(1))
      val rules = (children.drop(2) map { makeRule(_) }).flatten
      new MPRS(initialLHS, initialRHS, rules.toSet)
    }
    else {
      throw new IllegalTokenException("Expected a mPRS, got " + tokenType)
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
    val list = treeToSeq(result)
    val mprs = MPRSParser.fromAST(result)
    println(mprs)
    println("Actions: " + mprs.actions)
    println("Constants: " + mprs.constants)
    MVPDA.testRefinement(mprs)
  }

  try {
    val file = new File("src/main/resources/vpda_all_complete.xmts")
    val result = testFileForRefinement(file)
    if(result) {
      println(file + " refines")
      sys.exit(0)
    }
    else {
      println(file + " does not refine")
      sys.exit(0)
    }
  }
  catch {
    case e: IOException =>
      e.printStackTrace()
      sys.exit(-1)
    case e: RecognitionException =>
      e.printStackTrace()
      sys.exit(-2)
    case e: IllegalArgumentException =>
      e.printStackTrace()
      sys.exit(-3)
  }
}

