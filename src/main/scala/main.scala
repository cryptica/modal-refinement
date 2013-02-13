import org.antlr.runtime._
import org.antlr.runtime.tree.CommonTree;
import java.io.IOException
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer

case class IllegalTokenException(errorMsg: String) extends RuntimeException(errorMsg)

object MPRSParser {
  private def getChildren(ast: CommonTree) = {
    ast.getChildren.asScala map { _.asInstanceOf[CommonTree] }
  }
  private def makeAction(ast: CommonTree): String = {
    val token = ast.getToken
    val tokenType = token.getType
    tokenType match {
      case xMPRSParser.ACTION => token.getText
      case _ => throw new IllegalTokenException("Expected an action, got " + tokenType)
    }
  }
  private def makeRule(ast: CommonTree): RewriteRule = {
    val token = ast.getToken
    val tokenType = token.getType
    tokenType match {
      case xMPRSParser.MAY_RULE | xMPRSParser.MUST_RULE =>
        val children = getChildren(ast)
        val lhs = makeNormalProcess(children(0))
        val action = makeAction(children(1))
        val rhs = makeNormalProcess(children(2))
        tokenType match {
          case xMPRSParser.MAY_RULE =>
            new MayRule(lhs, action, rhs)
          case xMPRSParser.MUST_RULE =>
            new MustRule(lhs, action, rhs)
        }
      case _ => throw new IllegalTokenException("Expected a rule type, got " + tokenType)
    }
  }
  private def makeNormalProcess(ast: CommonTree) =
    Process.toNormalForm(makeProcess(ast))
  private def makeProcess(ast: CommonTree): Process = {
    val token = ast.getToken
    val tokenType = token.getType
    def getChildrenProcess() = getChildren(ast) map { makeProcess(_) }
    tokenType match {
      case xMPRSParser.EMPTY => Empty
      case xMPRSParser.CONSTANT => new Constant(token.getText)
      case xMPRSParser.PARALLEL => new Parallel(getChildrenProcess)
      case xMPRSParser.SEQUENTIAL => new Sequential(getChildrenProcess)
      case _ => throw new IllegalTokenException("Expected a process, got " + tokenType)
    }
  }

  def fromAST(ast: CommonTree): MPRS = {
    val token = ast.getToken
    val tokenType = token.getType
    if(tokenType == xMPRSParser.MPRS) {
      val children = getChildren(ast)
      val initial = makeNormalProcess(children.head)
      val rules = children.tail map { makeRule(_) }
      new MPRS(initial, rules)
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

  try {
    val input = getClass.getResource("simple_mprw.xmts")
    val lexer = new xMPRSLexer(new ANTLRInputStream((input.openStream())))
    val tokens = new CommonTokenStream(lexer)
    val parser = new xMPRSParser(tokens)
    val mprs = parser.mprs
    val result = mprs.tree.asInstanceOf[CommonTree];
    val list = treeToSeq(result)
    val mprsObject = MPRSParser.fromAST(result)
    println(mprsObject)
  }
  catch {
    case e: IOException => e.printStackTrace()
    case e: RecognitionException => e.printStackTrace()
  }
}

