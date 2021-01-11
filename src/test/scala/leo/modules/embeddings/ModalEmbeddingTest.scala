package leo
package modules
package embeddings

import leo.modules.input.TPTPParser
import org.scalatest.funsuite.AnyFunSuite

import java.io.File

class ModalEmbeddingTest  extends AnyFunSuite {
  private var testFiles: Seq[File] = new File(getClass.getResource("/").getPath).listFiles(_.isFile)

  println("###################################")
  println(s"Monomorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Monorphic ${filename.getName}") {
      println(s"Embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(ModalEmbedding.EmbeddingOption.MONOMORPHIC))
      transformed.foreach(t => println(t.pretty))
    }
  }

  println("###################################")
  println(s"Polymorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Polymorphic ${filename.getName}") {
      println(s"Embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(ModalEmbedding.EmbeddingOption.POLYMORPHIC))
      transformed.foreach(t => println(t.pretty))
    }
  }
}
