package leo
package modules
package embeddings

import org.scalatest.funsuite.AnyFunSuite
import java.io.File

import leo.modules.input.TPTPParser
import ModalEmbeddingOption._

class ModalEmbeddingTest  extends AnyFunSuite {
  private val testFiles: Seq[File] = new File(getClass.getResource("/").getPath).listFiles(_.isFile).toSeq

  println("###################################")
  println(s"Monomorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Monomorphic ${filename.getName}") {
      println(s"Monomorphic embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(MONOMORPHIC))
      transformed.foreach(t => println(t.pretty))
    }
  }

  println("###################################")
  println(s"Polymorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Polymorphic ${filename.getName}") {
      println(s"Polymorphic embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(POLYMORPHIC))
      transformed.foreach(t => println(t.pretty))
    }
  }
}
