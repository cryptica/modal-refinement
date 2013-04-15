import org.scalatest.FlatSpec
import java.io.File
import scala.collection.JavaConverters._

class VPDARefinementSpec extends FlatSpec {

  def getFilenamesFrom(folder: String) = {
    val en = getClass().getClassLoader().getResources(folder)
    if(en.hasMoreElements()) {
      val metaInf = en.nextElement()
      val fileMetaInf = new File(metaInf.toURI())
      fileMetaInf.listFiles().toList
    }
    else {
      Nil
    }
  }

  val posFiles = getFilenamesFrom("positive")
  posFiles foreach { file =>
    file.toString should "refine" in {
      assert(Main.testFileForRefinement(file))
    }
  }
  
  val negFiles = getFilenamesFrom("negative")
  negFiles foreach { file =>
    file.toString should "not refine" in {
      assert(!Main.testFileForRefinement(file))
    }
  }
}
