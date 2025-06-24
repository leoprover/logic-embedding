package leo.modules.embeddings

import leo.datastructures.TPTP

/** Embeddings that generate n output files (as opposed to [[Embedding]] where only one result is generated). */
trait EmbeddingN extends  Embedding {

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[OptionType#Value]): TPTP.Problem = throw new EmbeddingException("For n-ary embedding, use #applyN.")

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def applyN(problem: TPTP.Problem, embeddingOptions: Set[OptionType#Value]): Seq[TPTP.Problem]

  @throws[EmbeddingException]("if the embedding procedure could not be executed successfully.")
  def applyN(formulas: Seq[TPTP.AnnotatedFormula], embeddingOptions: Set[OptionType#Value]): Seq[Seq[TPTP.AnnotatedFormula]] =
    applyN(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).map(_.formulas)
}
