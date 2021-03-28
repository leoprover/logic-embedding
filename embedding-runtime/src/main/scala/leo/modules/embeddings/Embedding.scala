package leo.modules.embeddings

import leo.datastructures.TPTP
import leo.datastructures.TPTP.AnnotatedFormula

trait Embedding {
  type OptionType <: Enumeration

  def name: String
  def version: String

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(problem: Seq[AnnotatedFormula], embeddingOptions: Set[OptionType#Value]): Seq[AnnotatedFormula]

  def embeddingParameter: OptionType
  def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated
}
