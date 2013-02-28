import org.antlr.runtime._
import org.antlr.runtime.tree.CommonTree;
import java.io.IOException
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
          case xMPRSParser.MAY_RULE => MayRule
            List(new RewriteRule(MayRule, lhs, action, rhs))
          case xMPRSParser.MUST_RULE => MustRule
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

  try {
    //val input = getClass.getResource("simple_mprw.xmts")
    val input = getClass.getResource("vpda.xmts")
    //val input = getClass.getResource("rules_mprw.xmts")
    val lexer = new xMPRSLexer(new ANTLRInputStream((input.openStream())))
    val tokens = new CommonTokenStream(lexer)
    val parser = new xMPRSParser(tokens)
    val mprsTree = parser.mprs
    val result = mprsTree.tree.asInstanceOf[CommonTree];
    val list = treeToSeq(result)
    val mprs = MPRSParser.fromAST(result)
    println(mprs)
    if(mprs.isVPDA) {
      println("As vPDA:")
      mprs.asVPDA()
      println("Actions: " + mprs.actions)
      println("Constants: " + mprs.constants)
      val vpda = MVPDA.fromMPRS(mprs)
      println("Attack rules automaton:")
      println(vpda)
      println("Calculating fixpoint:")
      vpda.applyRules()
    }
  }
  catch {
    case e: IOException => e.printStackTrace()
    case e: RecognitionException => e.printStackTrace()
  }
}

