package leo.modules.embeddings

object Library {
  final def version: String = "1.9"

  def embeddingTable: Map[String, Embedding] = {
    Map(
      "$modal" -> ModalEmbedding,
      "$$modal_old" -> ModalLogicEmbeddingOld,
      "$alethic_modal" -> ModalEmbedding,
      "$deontic_modal" -> ModalEmbedding,
      "$epistemic_modal" -> ModalEmbedding,
      "$doxastic_modal" -> ModalEmbedding,
      "$temporal_instant" -> TemporalLogicEmbedding,
      "$$ddl" -> DyadicDeonticLogicEmbedding,
      "$$hybrid" -> HybridLogicEmbedding,
      "$$pal" -> PublicAnnouncementLogicEmbedding,
      "$$normative" -> NormativeDSLEmbedding,
      "$$fomlModel" -> FirstOrderManySortedToTXFEmbedding,
      "$$dhol" -> DHOLEmbedding,
      "$$dholtc" -> DHOLTCC
    )
  }
}
