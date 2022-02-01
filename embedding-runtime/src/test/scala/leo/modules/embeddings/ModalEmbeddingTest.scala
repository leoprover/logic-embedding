package leo
package modules
package embeddings

import org.scalatest.funsuite.AnyFunSuite

import leo.modules.input.TPTPParser
import ModalEmbedding.ModalEmbeddingOption._

class ModalEmbeddingTest  extends AnyFunSuite {
  private val modalTHF: Seq[String] = Seq("LCL870#1.p")

  for (problemName <- modalTHF) {
    test(problemName) {
      val source = io.Source.fromResource(s"$problemName")
      try {
        val input = TPTPParser.problem(source)
        val transformed = ModalEmbedding.apply(input, Set.empty)
        transformed.formulas.foreach(t => println(t.pretty))
      } catch {
        case e: TPTPParser.TPTPParseException => println(s"Parse error at ${e.line}:${e.offset}: ${e.getMessage}")
          throw e
      }

    }
  }

}
