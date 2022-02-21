package leo.modules.embeddings

object Library {
  final def version: String = "1.3"

  def embeddingTable: Map[String, Embedding] = {
    Map(
      "$$dhol" -> DHOLEmbedding,
      "$modal" -> ModalEmbedding,
      "$alethic_modal" -> ModalEmbedding,
      "$deontic_modal" -> ModalEmbedding,
      "$epistemic_modal" -> ModalEmbedding,
      "$$ddl" -> DyadicDeonticLogicEmbedding,
      "$$hybrid" -> HybridLogicEmbedding,
      "$$pal" -> PublicAnnouncementLogicEmbedding
    )
  }
}
