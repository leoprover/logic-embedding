package leo.modules.embeddings

import leo.datastructures.TPTP

trait Embedding {
  type OptionType <: Enumeration

  def name: String
  def version: String

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(problem: TPTP.Problem, embeddingOptions: Set[OptionType#Value]): TPTP.Problem

  def embeddingParameter: OptionType
  def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated
}
