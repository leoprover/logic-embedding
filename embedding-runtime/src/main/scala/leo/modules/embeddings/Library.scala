package leo.modules.embeddings

object Library {
  final def version: String = "1.1"

  def embeddingTable: Map[String, Embedding] = {
    Map(
      "modal" -> ModalEmbedding
    )
  }
}
