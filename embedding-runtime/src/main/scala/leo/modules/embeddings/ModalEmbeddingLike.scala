package leo.modules.embeddings

/**
 * Collection of definitions that may be relevant for different modal-like embeddings.
 */
trait ModalEmbeddingLike {
  abstract sealed class Parameter
  case object MONOMORPHIC extends Parameter
  case object POLYMORPHIC extends Parameter
  case object MODALITIES_SEMANTICAL extends Parameter
  case object MODALITIES_SYNTACTICAL extends Parameter
  case object DOMAINS_SEMANTICAL extends Parameter
  case object DOMAINS_SYNTACTICAL extends Parameter
  case object FORCE_HIGHERORDER extends Parameter
  case object ALLOW_EMPTY_DOMAINS extends Parameter
  case object SILENT extends Parameter
  case object NO_UNIVERSAL_S5 extends Parameter

  object Parameter extends Embedding.EmbeddingParameter[Parameter] {
    override def valueOf(s: String): Option[Parameter] = s match {
      case "MONOMORPHIC" => Some(MONOMORPHIC)
      case "POLYMORPHIC" => Some(POLYMORPHIC)
      case "MODALITIES_SEMANTICAL" => Some(MODALITIES_SEMANTICAL)
      case "MODALITIES_SYNTACTICAL" => Some(MODALITIES_SYNTACTICAL)
      case "DOMAINS_SEMANTICAL" => Some(DOMAINS_SEMANTICAL)
      case "DOMAINS_SYNTACTICAL" => Some(DOMAINS_SYNTACTICAL)
      case "FORCE_HIGHERORDER" => Some(FORCE_HIGHERORDER)
      case "ALLOW_EMPTY_DOMAINS" => Some(ALLOW_EMPTY_DOMAINS)
      case "SILENT" => Some(SILENT)
      case "NO_UNIVERSAL_S5" => Some(NO_UNIVERSAL_S5)
      case _ => None
    }
    override def values: Set[Parameter] = supportedParameters
  }
  protected def supportedParameters: Set[Parameter] = Set(MONOMORPHIC, POLYMORPHIC, MODALITIES_SEMANTICAL,
    MODALITIES_SYNTACTICAL, DOMAINS_SEMANTICAL, DOMAINS_SYNTACTICAL, FORCE_HIGHERORDER,
    ALLOW_EMPTY_DOMAINS, SILENT, NO_UNIVERSAL_S5)

  type EmbeddingParameterType = Parameter
  final def embeddingParameter: Embedding.EmbeddingParameter[Parameter] = Parameter

  protected final val allowedModalLogicNames: Seq[String] = Seq("$modal", "$alethic_modal", "$deontic_modal", "$epistemic_modal", "$doxastic_modal")
  protected final val synonymsForBox: Seq[String] = Seq("$box","$necessary","$obligatory","$knows","$believes")
  protected final val synonymsForDiamond: Seq[String] = Seq("$dia","$possible","$permissible","$canKnow","$canBelieve")

  protected final val logicSpecParamNameTermLocality = "$terms"
  protected sealed abstract class TermLocality
  protected final case object Local extends TermLocality
  protected final case object Global extends TermLocality

  protected final val logicSpecParamNameRigidity = "$designation"
  protected sealed abstract class Rigidity
  protected final case object Rigid extends Rigidity
  protected final case object Flexible extends Rigidity

  protected final val logicSpecParamNameQuantification = "$domains"
  protected sealed abstract class DomainType
  protected final case object ConstantDomain extends DomainType
  protected final case object VaryingDomain extends DomainType
  protected final case object CumulativeDomain extends DomainType
  protected final case object DecreasingDomain extends DomainType

  protected final val logicSpecParamNameModalities = "$modalities"
  protected final def isModalAxiomName(name: String): Boolean = name.startsWith("$modal_axiom_")
  protected final def isModalSystemName(name: String): Boolean = name.startsWith("$modal_system_")

  protected final val modalSystemTable: Map[String, Seq[String]] = Map(
    "$modal_system_K" -> Seq("$modal_axiom_K"),
    "$modal_system_K4" -> Seq("$modal_axiom_K", "$modal_axiom_4"),
    "$modal_system_K5" -> Seq("$modal_axiom_K", "$modal_axiom_5"),
    "$modal_system_KB" -> Seq("$modal_axiom_K", "$modal_axiom_B"),
    "$modal_system_K45" -> Seq("$modal_axiom_K", "$modal_axiom_4", "$modal_axiom_5"),
    "$modal_system_KB5" -> Seq("$modal_axiom_K", "$modal_axiom_B", "$modal_axiom_5"),
    "$modal_system_D" -> Seq("$modal_axiom_K", "$modal_axiom_D"),
    "$modal_system_D4" -> Seq("$modal_axiom_K", "$modal_axiom_D", "$modal_axiom_4"),
    "$modal_system_D5" -> Seq("$modal_axiom_K", "$modal_axiom_D", "$modal_axiom_5"),
    "$modal_system_D45" -> Seq("$modal_axiom_K", "$modal_axiom_D", "$modal_axiom_4", "$modal_axiom_5"),
    "$modal_system_DB" -> Seq("$modal_axiom_K", "$modal_axiom_D", "$modal_axiom_B"),
    "$modal_system_T" -> Seq("$modal_axiom_K", "$modal_axiom_T"),
    "$modal_system_M" -> Seq("$modal_axiom_K", "$modal_axiom_T"),
    "$modal_system_B" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_B"),
    "$modal_system_S4" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4"),
    "$modal_system_S5" -> Seq("$modal_axiom_K", "$modal_axiom_S5U"),
    "$modal_system_S5_equiv_relation" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_5"), /* special system for use in multi-modal S5 */
    "$modal_system_K4W" -> Seq("$modal_axiom_K", "$modal_axiom_GL"),
    "$modal_system_4_1" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_H"),
    "$modal_system_4_2" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_M"),
    "$modal_system_4_3" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_G"),
    "$modal_system_Grz" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_Grz"),
    "$modal_system_GL" -> Seq("$modal_axiom_K", "$modal_axiom_GL")
  )

  protected final val logicSpecParamNames: Seq[String] = Seq(logicSpecParamNameTermLocality, logicSpecParamNameRigidity,
    logicSpecParamNameQuantification, logicSpecParamNameModalities)
}
