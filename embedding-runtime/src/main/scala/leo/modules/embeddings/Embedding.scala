package leo.modules.embeddings

import leo.datastructures.TPTP

/** Embeddings that generates exactly one output file (as opposed to [[EmbeddingN]] where n results are generated). */
trait Embedding {
  /** The type of parameter options provided by the embedding instance. */
  type OptionType <: Enumeration

  /** The name of the embedding */
  def name: String
  /** The version number of the embedding instance implementation. */
  def version: String

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(problem: TPTP.Problem, embeddingOptions: Set[OptionType#Value]): TPTP.Problem

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(formulas: Seq[TPTP.AnnotatedFormula], embeddingOptions: Set[OptionType#Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  /** The enumeration object of this embedding's parameter values. */
  def embeddingParameter: OptionType
  /** Given the specification `specs` construct a valid TPTP logic specification for the logic
   * targeted by this embedding. */
  def generateSpecification(specs: Map[String, String]): TPTP.AnnotatedFormula
}
