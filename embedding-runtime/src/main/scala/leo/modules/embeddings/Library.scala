package leo.modules.embeddings

object Library {
  final def version: String = "1.2"

  def embeddingTable: Map[String, Embedding] = {
    Map(
      "modal" -> ModalEmbedding,
      "alethic_modal" -> ModalEmbedding,
      "deontic_modal" -> ModalEmbedding,
      "epistemic_modal" -> ModalEmbedding
    )
  }
}
