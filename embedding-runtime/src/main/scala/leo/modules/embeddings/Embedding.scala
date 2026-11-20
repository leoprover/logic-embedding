package leo.modules.embeddings

import leo.datastructures.TPTP

/** Embeddings that generates exactly one output file (as opposed to [[EmbeddingN]] where n results are generated). */
trait Embedding {
  import Embedding.EmbeddingParameter

  type EmbeddingParameterType
  /** The name of the embedding */
  def name: String
  /** The version number of the embedding instance implementation. */
  def version: String

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(problem: TPTP.Problem, embeddingOptions: Set[EmbeddingParameterType]): TPTP.Problem

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def apply(formulas: Seq[TPTP.AnnotatedFormula], embeddingOptions: Set[EmbeddingParameterType]): Seq[TPTP.AnnotatedFormula] = {
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas
  }

  /** The enumeration object of this embedding's parameter values. */
  def embeddingParameter: EmbeddingParameter[EmbeddingParameterType]
  /** Given the specification `specs` construct a valid TPTP logic specification for the logic
   * targeted by this embedding. */
  def generateSpecification(specs: Map[String, String]): TPTP.AnnotatedFormula
}
trait NoEmbeddingParameters {
  import leo.modules.embeddings.Embedding.EmbeddingParameter

  type EmbeddingParameterType = Nothing
  def embeddingParameter: EmbeddingParameter[EmbeddingParameterType] = Embedding.NoEmbeddingParameter
}
object Embedding {
  trait EmbeddingParameter[A] {
    def valueOf(s: String): Option[A]
    def values: Set[A]
  }
  object NoEmbeddingParameter extends EmbeddingParameter[Nothing] {
    override def valueOf(s: String): Option[Nothing] = None
    override def values: Set[Nothing] = Set.empty
  }
}