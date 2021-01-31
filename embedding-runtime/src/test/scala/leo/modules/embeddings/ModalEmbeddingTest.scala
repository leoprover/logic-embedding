package leo
package modules
package embeddings

import org.scalatest.funsuite.AnyFunSuite
import java.io.File

import leo.modules.input.TPTPParser
import ModalEmbedding.ModalEmbeddingOption._

class ModalEmbeddingTest  extends AnyFunSuite {
  private val testFiles: Seq[File] = new File(getClass.getResource("/").getPath).listFiles(_.isFile).toSeq

  println("###################################")
  println(s"Monomorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Monomorphic semantical ${filename.getName}") {
      println(s"Monomorphic semantical embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(MONOMORPHIC, MODALITIES_SEMANTICAL))
      transformed.foreach(t => println(t.pretty))
    }
  }

  for (filename <- testFiles) {
    test(s"Monomorphic syntactical ${filename.getName}") {
      println(s"Monomorphic syntactical embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(MONOMORPHIC, MODALITIES_SYNTACTICAL))
      transformed.foreach(t => println(t.pretty))
    }
  }

  println("###################################")
  println(s"Polymorphic embedding tests ...")
  println("###################################")

  for (filename <- testFiles) {
    test(s"Polymorphic semantical ${filename.getName}") {
      println(s"Polymorphic semantical embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(POLYMORPHIC, MODALITIES_SEMANTICAL))
      transformed.foreach(t => println(t.pretty))
    }
  }

  for (filename <- testFiles) {
    test(s"Polymorphic syntactical ${filename.getName}") {
      println(s"Polymorphic syntactical embedding ${filename.getName} ...")
      val file = io.Source.fromFile(filename.getAbsolutePath)
      val input = TPTPParser.problem(file)
      val transformed = ModalEmbedding.apply(input.formulas, Set(POLYMORPHIC, MODALITIES_SYNTACTICAL))
      transformed.foreach(t => println(t.pretty))
    }
  }
}
