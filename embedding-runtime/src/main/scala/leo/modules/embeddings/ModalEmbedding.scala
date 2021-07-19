package leo
package modules
package embeddings

import datastructures.{FlexMap, TPTP}
import TPTP.{AnnotatedFormula, THF}

import scala.collection.immutable.{AbstractSeq, LinearSeq}

object ModalEmbedding extends Embedding {
  object ModalEmbeddingOption extends Enumeration {
    // Hidden on purpose, to allow distinction between the object itself and its values.
    //    type ModalEmbeddingOption = Value
    final val MONOMORPHIC, POLYMORPHIC,
    MODALITIES_SEMANTICAL, MODALITIES_SYNTACTICAL,
    DOMAINS_SEMANTICAL, DOMAINS_SYNTACTICAL = Value
  }

  override type OptionType = ModalEmbeddingOption.type
  override final def embeddingParameter: ModalEmbeddingOption.type = ModalEmbeddingOption

  override final def name: String = "modal"
  override final def version: String = "1.1"

  private[this] final val defaultConstantSpec = "$rigid"
  private[this] final val defaultQuantificationSpec = "$constant"
  private[this] final val defaultConsequenceSpec = "$global"
  private[this] final val defaultModalitiesSpec = "$modal_system_K"
  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated = {
    import modules.input.TPTPParser.annotatedTHF
    val spec: StringBuilder = new StringBuilder
    spec.append("thf(logic_spec, logic, (")
    spec.append("$modal := [")
    spec.append("$constants := "); spec.append(specs.getOrElse("$constants", defaultConstantSpec)); spec.append(",")
    spec.append("$quantification := "); spec.append(specs.getOrElse("$quantification", defaultQuantificationSpec)); spec.append(",")
    spec.append("$consequence := "); spec.append(specs.getOrElse("$consequence", defaultConsequenceSpec)); spec.append(",")
    spec.append("$modalities := "); spec.append(specs.getOrElse("$modalities", defaultModalitiesSpec))
    spec.append("] )).")
    annotatedTHF(spec.toString)
  }

  override final def apply(problem: Seq[AnnotatedFormula],
                  embeddingOptions: Set[ModalEmbeddingOption.Value] = Set.empty): Seq[AnnotatedFormula] =
    new ModalEmbeddingImpl(problem, embeddingOptions).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class ModalEmbeddingImpl(problem: Seq[AnnotatedFormula], embeddingOptions: Set[ModalEmbeddingOption.Value]) {
    import ModalEmbeddingOption._

    ///////////////////////////////////////////////////////////////////
    private final val state = FlexMap.apply()

    // Semantics dimensions
    private final val RIGIDITY_RIGID = true
    private final val RIGIDITY_FLEXIBLE = false
    private final val RIGIDITY = state.createKey[String, Boolean]()
    state(RIGIDITY) += ("$o" -> RIGIDITY_FLEXIBLE) // FIXME: rigidity is bound to constants, not types.

    private final val CONSEQUENCE_GLOBAL = true
    private final val CONSEQUENCE_LOCAL = false
    private final val CONSEQUENCE = state.createKey[String, Boolean]()

    private final val DOMAIN_CONSTANT = 0
    private final val DOMAIN_VARYING = 1
    private final val DOMAIN_CUMULATIVE = 2
    private final val DOMAIN_DECREASING = 3
    private final val DOMAIN = state.createKey[String, Int]()

    private final val MODALS = state.createKey[THF.Formula, Seq[String]]()
    ////////////////////////////////////////////////////////////////////
    // Embedding options
    private val polymorphic: Boolean = embeddingOptions.contains(POLYMORPHIC) // default monomorphic

    private final val MODALITY_EMBEDDING_SYNTACTICAL = true
    private final val MODALITY_EMBEDDING_SEMANTICAL = false
    private val modalityEmbeddingType: Boolean = embeddingOptions.contains(MODALITIES_SYNTACTICAL) // default semantical

    private final val DOMAINS_EMBEDDING_SYNTACTICAL = true
    private final val DOMAINS_EMBEDDING_SEMANTICAL = false
    private val domainEmbeddingType: Boolean = embeddingOptions.contains(DOMAINS_SYNTACTICAL) // default semantical
    ////////////////////////////////////////////////////////////////////

    def apply(): Seq[AnnotatedFormula] = {
      val (spec, remainingFormulas) = splitInput(problem)
      createState(spec)
      val (typeFormulas, nonTypeFormulas) = remainingFormulas.partition(_.role == "type")
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedOtherFormulas = nonTypeFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      generatedMetaFormulas ++ convertedTypeFormulas ++ convertedOtherFormulas
    }

    def convertAnnotatedFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Logical(formula), annotations) =>
          val convertedFormula0 = convertFormula(formula)
          val convertedFormula = state(CONSEQUENCE)(name) match {
            case CONSEQUENCE_GLOBAL => THF.BinaryFormula(THF.App, mglobal, convertedFormula0)
            case CONSEQUENCE_LOCAL => THF.BinaryFormula(THF.App, mlocal, convertedFormula0)
          }
          TPTP.THFAnnotated(name, role, TPTP.THF.Logical(convertedFormula), annotations)
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private def mkLambda(variable: THF.TypedVariable, body: THF.Formula): THF.Formula = {
      THF.QuantifiedFormula(THF.^, Seq(variable), body)
    }

    private def mkSingleQuantified(quantifier: THF.Quantifier)(variable: THF.TypedVariable, acc: THF.Formula): THF.Formula = {
      val convertedVariable: THF.TypedVariable = (variable._1, convertType(variable._2))
      quantifierType(convertedVariable._2)
      val convertedQuantifier: THF.Formula =
        if (polymorphic) THF.BinaryFormula(THF.App, convertQuantifier(quantifier, variable._2, convertedVariable._2), convertedVariable._2)
        else convertQuantifier(quantifier, variable._2, convertedVariable._2)
      THF.BinaryFormula(THF.App, convertedQuantifier, mkLambda(convertedVariable, acc))
    }

    private def convertFormula(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
      import TPTP.THF.App
      import modules.input.TPTPParser.thf

      formula match {
        /* ######################################### */
        /* TPTP defined constants that need to be handled specially*/
        // Nullary: $true and $false -> (^[W:mworld]: $true) resp. (^[W:mworld]: $false)
        case THF.FunctionTerm(f, Seq()) if Seq("$true", "$false").contains(f) =>
          thf(s"^[W: $worldTypeName]: $f")

        // Binary: $less, $lesseq, $greater, $greatereq -> (^[W:mworld]: ...) as they are rigid constants.
          // This will not work for partially applied function expressions, e.g. (f @ $greater).
          // but the embedding will be much more complicated when we support this, as $greater and friends
          // are ad-hoc polymorphic and would need to be embedded to ^[X:T, Y:T, W:mworld]: ($greater @ X @ Y)
          // but we don't know what T is supposed to be. And just embedding $greater to ^[W:mworld]: $greater
          // will not be type-correct.
        case THF.BinaryFormula(App, THF.BinaryFormula(App, THF.FunctionTerm(f, Seq()), left), right)
          if Seq("$less", "$lesseq", "$greater", "$greatereq").contains(f) =>

          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          thf(s"^[W:$worldTypeName]: ($f @ (${convertedLeft.pretty}) @ (${convertedRight.pretty}))")

        /* ######################################### */
        /* Standard cases: Recurse embedding. */
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertFormula)
          THF.FunctionTerm(f, convertedArgs)

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedBody = convertFormula(body)
          variableList.foldRight(convertedBody)(mkSingleQuantified(quantifier))

        case THF.Variable(_) => formula

        case THF.UnaryFormula(connective, body) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedBody: TPTP.THF.Formula = convertFormula(body)
          THF.BinaryFormula(App, convertedConnective, convertedBody)

        case THF.BinaryFormula(App, left, right) =>
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, convertedLeft, convertedRight)

        /* The following case also subsumes where `connective` is a non-classical connective. */
        case THF.BinaryFormula(connective, left, right) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, THF.BinaryFormula(App, convertedConnective, convertedLeft), convertedRight)

        case THF.ConnectiveTerm(conn) => convertConnective(conn) // TODO

        case c@THF.DefinedTH1ConstantTerm(_) => c // TODO

        case THF.Tuple(elements) =>
          val convertedElements: Seq[TPTP.THF.Formula] = elements.map(convertFormula)
          THF.Tuple(convertedElements)

        case THF.ConditionalTerm(condition, thn, els) =>
          val convertedCondition: TPTP.THF.Formula = convertFormula(condition)
          val convertedThn: TPTP.THF.Formula = convertFormula(thn)
          val convertedEls: TPTP.THF.Formula = convertFormula(els)
          THF.ConditionalTerm(convertedCondition, convertedThn, convertedEls)

        case THF.LetTerm(typing, binding, body) => // This will probably change as the parse tree of LetTerms will still change.
          val convertedTyping: Map[String, TPTP.THF.Type] = typing.map(a => (a._1, convertType(a._2)))
          val convertedBinding: Seq[(TPTP.THF.Formula, TPTP.THF.Formula)] = binding.map(a => (convertFormula(a._1), convertFormula(a._2)))
          val convertedBody = convertFormula(body)
          THF.LetTerm(convertedTyping, convertedBinding, convertedBody)
        case THF.DistinctObject(_) => formula
        case THF.NumberTerm(_) => formula
      }
    }

    @inline private[this] def str2Fun(functionName: String): THF.Formula = THF.FunctionTerm(functionName, Seq.empty)
    private[this] def convertConnective(connective: TPTP.THF.Connective): THF.Formula = {
      connective match {
        case THF.~ => str2Fun("mnot")
        case THF.Eq => str2Fun("meq")
        case THF.Neq => str2Fun("mneq")
        case THF.<=> => str2Fun("mequiv")
        case THF.Impl => str2Fun("mimplies")
        case THF.<= => str2Fun("mif")
        case THF.<~> => str2Fun("mniff")
        case THF.~| => str2Fun("mnor")
        case THF.~& => str2Fun("mnand")
        case THF.| => str2Fun("mor")
        case THF.& => str2Fun("mand")
        /// Non-classical connectives BEGIN
          // Box operator
        case THF.NonclassicalBox(index) => index match {
          case Some(index0) =>
            val typeOfIndex = getTypeOfIndex(index0)
            mboxIndexed(index0, typeOfIndex)
          case None => str2Fun("mbox")
        }
        case THF.NonclassicalLongOperator("$box", parameters) => parameters match {
          case Seq() => str2Fun("mbox")
          case Seq(Left(index0)) =>
            val typeOfIndex = getTypeOfIndex(index0)
            mboxIndexed(index0, typeOfIndex)
          case _ => throw new EmbeddingException(s"Only up to one index is allowed in box operator, but parameters '${parameters.toString()}' was given.")
        }
        // Diamond operator
        case THF.NonclassicalDiamond(index) => index match {
          case Some(index0) =>
            val typeOfIndex = getTypeOfIndex(index0)
            mdiaIndexed(index0, typeOfIndex)
          case None => str2Fun("mdia")
        }
        case THF.NonclassicalLongOperator("$dia", parameters) => parameters match {
          case Seq() => str2Fun("mdia")
          case Seq(Left(index0)) =>
            val typeOfIndex = getTypeOfIndex(index0)
            mdiaIndexed(index0, typeOfIndex)
          case _ => throw new EmbeddingException(s"Only up to one index is allowed in diamond operator, but parameters '${parameters.toString()}' was given.")
        }
        /// Non-classical connectives END
        case THF.App => throw new EmbeddingException(s"An unexpected error occurred, this is considered a bug. Please report it :-)")
        case THF.:= => throw new EmbeddingException(s"Unexpected assignment operator used as connective.")
        case _ => throw new EmbeddingException(s"Unexpected type constructor used as connective: '${connective.pretty}'")
      }
    }

    private[this] def getTypeOfIndex(index0: THF.Formula): THF.Type = {
      index0 match {
        case ft@THF.FunctionTerm(f, Seq()) if ft.isDefinedFunction => f match {
          case "$true" | "$false" => str2Fun("$o")
          case _ => throw new EmbeddingException(s"Unknown defined functor '$f' used as index; type unknown. Please define its type explicitly.")
        }
        case THF.FunctionTerm(f, Seq()) =>
          if (typedSymbolsInOriginalProblem.contains(f)) typedSymbolsInOriginalProblem(f)
          else throw new EmbeddingException(s"Unknown functor '$f' used as index; type unknown. Please define its type explicitly.")
        case THF.Variable(name) => ??? // TODO. Find out by recursive term structure
        case THF.DistinctObject(_) => str2Fun("$i")
        case THF.NumberTerm(number) => number match {
          case TPTP.Integer(_) => str2Fun("$int")
          case _ => throw new EmbeddingException(s"Only integers are allowed as index, but '${number.pretty}' was given.")
        }
        case _ => throw new EmbeddingException(s"Only constants are allowed as index, but complex term '${index0.pretty}' was given. Consider using a long form connective instead.")
      }
    }

    private def convertQuantifier(quantifier: TPTP.THF.Quantifier, typ: TPTP.THF.Type, convertedType: TPTP.THF.Type): THF.Formula = {
      val name = quantifier match {
        case THF.! =>
          try {
            state(DOMAIN)(typ.pretty) match {
              case DOMAIN_CONSTANT => if (polymorphic) "mforall_const" else s"mforall_${serializeType(convertedType)}"
              case _ => // all three other cases
                if (polymorphic) "mforall_vary" else s"mforall_${serializeType(convertedType)}"
            }
          } catch {
            case _: NoSuchElementException => throw new EmbeddingException(s"Undefined domain semantics for type '${typ.pretty}'. Maybe a default value was omitted?")
          }

        case THF.? =>
          try {
            state(DOMAIN)(typ.pretty) match {
              case DOMAIN_CONSTANT => if (polymorphic) "mexists_const" else s"mexists_${serializeType(convertedType)}"
              case _ => // all three other cases
                if (polymorphic) "mexists_vary" else s"mexists_${serializeType(convertedType)}"
            }
          } catch {
            case _: NoSuchElementException => throw new EmbeddingException(s"Undefined domain semantics for type '${typ.pretty}'. Maybe a default value was omitted?")
          }
        case THF.^ => "mlambda"
        case THF.@+ => "mchoice"
        case THF.@- => "mdescription"
        case _ => throw new EmbeddingException(s"Unexpected type quantifier used as term quantifier: '${quantifier.pretty}'")
      }
      THF.FunctionTerm(name, Seq.empty)
    }

    @inline private[this] def mbox: THF.Formula = str2Fun("mbox")
    private[this] def mboxIndexed(index: THF.Formula, typ: THF.Type): THF.Formula = {
      // TODO: Switch $int -> otherType here
      multiModal(index, typ)
      if (polymorphic) THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, mbox, typ), index)
      else THF.BinaryFormula(THF.App, THF.FunctionTerm(s"mbox_${serializeType(typ)}", Seq.empty), index)
    }
    private[this] def mdia: THF.Formula = THF.FunctionTerm("mdia", Seq.empty)
    private[this] def mdiaIndexed(index: THF.Formula, typ: THF.Type): THF.Formula = {
      // TODO: Switch $int -> otherType here
      multiModal(index, typ)
      if (polymorphic) THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, mdia, typ), index)
      else THF.BinaryFormula(THF.App, THF.FunctionTerm(s"mdia_${serializeType(typ)}", Seq.empty), index)
    }

    private[this] def mglobal: THF.Formula = THF.FunctionTerm("mglobal", Seq.empty)
    private[this] def mlocal: THF.Formula =  THF.FunctionTerm("mlocal", Seq.empty)

    private def convertTypeFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedTyping = TPTP.THF.Typing(symbol, convertType(typ))
          typedSymbolsInOriginalProblem += (symbol -> typ)
          TPTP.THFAnnotated(name, role, convertedTyping, annotations)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertType)
          if (state(RIGIDITY)(f)) THF.FunctionTerm(f, convertedArgs)
          else THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), THF.FunctionTerm(f, convertedArgs))

        case THF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertType(left)
          val convertedRight = convertType(right)
          THF.BinaryFormula(connective, convertedLeft, convertedRight)

        case THF.Tuple(elements) =>
          val convertedElements = elements.map(convertType)
          THF.Tuple(convertedElements)

        case _ => throw new EmbeddingException(s"Unexpected type expression in type: '${typ.pretty}'")
      }
    }

    ///////////////////////////////////////////////////
    // Local embedding state
    ///////////////////////////////////////////////////
    import collection.mutable
    private[this] val typedSymbolsInOriginalProblem: mutable.Map[String, THF.Type] = mutable.Map.empty
    private[this] val modalOperators: mutable.Map[THF.Type, Set[THF.Formula]] = mutable.Map.empty
    private[this] def isMultiModal: Boolean = modalOperators.nonEmpty
    private[this] def multiModal(index: THF.Formula, typ: THF.Type): Unit = {
      val set = modalOperators.getOrElse(typ, Set.empty)
      modalOperators += (typ -> (set + index))
    }

    private[this] val quantifierTypes: mutable.Set[THF.Type] = mutable.Set.empty
    private[this] def quantifierType(typ: THF.Type): Unit = {
      quantifierTypes += typ
    }

    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty
      /////////////////////////////////////////////////////////////
      // First: Introduce world type
      result.append(worldTypeTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Introduce mrel (as relation or as collection of relations)
      if (isMultiModal) {
        if (polymorphic) result.append(polyIndexedAccessibilityRelationTPTPDef())
        else modalOperators foreach { case (ty, _) => result.append(indexedAccessibilityRelationTPTPDef(ty)) }
      } else result.append(simpleAccessibilityRelationTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define mglobal/mlocal
      state.getDefault(CONSEQUENCE) match {
        case Some(consequence) => consequence match { // Add default and the other one if used
          case CONSEQUENCE_GLOBAL =>
            result.appendAll(mglobalTPTPDef())
            if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mlocalTPTPDef())
          case CONSEQUENCE_LOCAL =>
            result.appendAll(mlocalTPTPDef())
            if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_GLOBAL) ||
              modalityEmbeddingType == MODALITY_EMBEDDING_SYNTACTICAL ||
              domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL) result.appendAll(mglobalTPTPDef())
        }
        case None => // Add only those used
          if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_GLOBAL) ||
            modalityEmbeddingType == MODALITY_EMBEDDING_SYNTACTICAL ||
            domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL) result.appendAll(mglobalTPTPDef())
          if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mlocalTPTPDef())
      }
      /////////////////////////////////////////////////////////////
      // Then: Define connectives
      result.appendAll(connectivesTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define modal operators
      if (isMultiModal) {
        if (polymorphic) result.appendAll(polyIndexedModalOperatorsTPTPDef())
        else modalOperators foreach { case (ty, _) => result.appendAll(indexedModalOperatorsTPTPDef(ty)) }
      } else result.appendAll(simpleModalOperatorsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Give mrel properties (sem/syn)
      // write used properties and assign (if semantical)
      // or write syntactical axioms (if syntactical)
      if (isMultiModal) {
        val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) {
          if (polymorphic) polyIndexedSemanticAxiomTable else indexedSemanticAxiomTable
        } else {
          if (polymorphic) polyIndexedSyntacticAxiomTable else indexedSyntacticAxiomTable
        }
        modalOperators foreach { case (ty, idxs) =>
          idxs foreach { idx =>
            val modalSystem = state(MODALS).apply(idx)
            val axiomNames = if (isModalSystemName(modalSystem.head)) modalSystemTable(modalSystem.head) else modalSystem
            axiomNames foreach { ax =>
              val axiom = axiomTable.apply(ax)
              axiom.foreach{ f =>
                val res = f(idx, ty)
                result.append(res)
              }
            }
          }
        }
      } else {
        val modalSystem = state.getDefault(MODALS)
        modalSystem match {
          case Some(value) =>
            val axiomNames = if (isModalSystemName(value.head)) modalSystemTable(value.head) else value
            val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) semanticAxiomTable else syntacticAxiomTable
            val modalAxioms = axiomNames.flatMap(axiomTable).toSet
            result.appendAll(modalAxioms)
          case None => throw new EmbeddingException(s"No semantics for modal operators specified, embedding not possible.")
        }
      }
      /////////////////////////////////////////////////////////////
      // Then: Define exist-in-world-predicates and quantifier restrictions (if cumul/decr/vary and semantic embedding)
      // In case of syntactical embedding, we need to have the quantifier symbols defined first.
      if (polymorphic) {
        if (quantifierTypes.nonEmpty) {
          if (quantifierTypes.exists(ty => state(DOMAIN)(ty.pretty) != DOMAIN_CONSTANT))
            result.appendAll(polyIndexedExistsInWorldTPTPDef()) // define poly eiw
          if (domainEmbeddingType == DOMAINS_EMBEDDING_SEMANTICAL) {
            quantifierTypes foreach { ty =>
              if (state(DOMAIN)(ty.pretty) == DOMAIN_CUMULATIVE)
                result.appendAll(polyIndexedCumulativeExistsInWorldTPTPDef(ty)) // define cumul axioms for eiw with that type
              if (state(DOMAIN)(ty.pretty) == DOMAIN_DECREASING)
                result.appendAll(polyIndexedDecreasingExistsInWorldTPTPDef(ty)) // define decreasing axioms for eiw with that type
            }
          }
        }
      } else {
        quantifierTypes foreach { ty =>
          if (state(DOMAIN)(ty.pretty) != DOMAIN_CONSTANT) {
            result.appendAll(indexedExistsInWorldTPTPDef(ty)) // define eiw with standard axioms
          }
          if (domainEmbeddingType == DOMAINS_EMBEDDING_SEMANTICAL) {
            if (state(DOMAIN)(ty.pretty) == DOMAIN_CUMULATIVE)
              result.appendAll(indexedCumulativeExistsInWorldTPTPDef(ty)) // define cumul axioms for eiw
            else if (state(DOMAIN)(ty.pretty) == DOMAIN_DECREASING)
              result.appendAll(indexedDecreasingExistsInWorldTPTPDef(ty)) // define decreasing axioms for eiw
          }
        }
      }
      /////////////////////////////////////////////////////////////
      // Then: Define quantifiers (TH0/TH1)
      if (polymorphic) {
        if (quantifierTypes.nonEmpty) {
          if (quantifierTypes.exists(ty => state(DOMAIN)(ty.pretty) == DOMAIN_CONSTANT))
            result.appendAll(polyIndexedConstQuantifierTPTPDef())
          if (quantifierTypes.exists(ty => state(DOMAIN)(ty.pretty) != DOMAIN_CONSTANT))
            result.appendAll(polyIndexedVaryQuantifierTPTPDef())
          if (domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL) {
            // in case of syntactical embedding: write restrictions using CBF resp. BF now.
            quantifierTypes foreach { ty =>
              if (state(DOMAIN)(ty.pretty) == DOMAIN_CUMULATIVE) {
                result.appendAll(indexedConverseBarcanFormulaTPTPDef(ty))
              } else if (state(DOMAIN)(ty.pretty) == DOMAIN_DECREASING) {
                result.appendAll(indexedBarcanFormulaTPTPDef(ty))
              }
            }
          }
        }
      } else {
        quantifierTypes foreach { ty =>
          if (state(DOMAIN)(ty.pretty) == DOMAIN_CONSTANT) result.appendAll(indexedConstQuantifierTPTPDef(ty))
          else {
            result.appendAll(indexedVaryQuantifierTPTPDef(ty))
            if (domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL) {
              // in case of syntactical embedding: write restrictions using CBF resp. BF now.
              if (state(DOMAIN)(ty.pretty) == DOMAIN_CUMULATIVE) {
                result.appendAll(indexedConverseBarcanFormulaTPTPDef(ty))
              } else if (state(DOMAIN)(ty.pretty) == DOMAIN_DECREASING) {
                result.appendAll(indexedBarcanFormulaTPTPDef(ty))
              }
            }
          }
        }
      }
      /////////////////////////////////////////////////////////////
      // Return all
      result.toSeq
    }

    @inline private[this] def worldTypeName: String = "mworld"

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($worldTypeName, type, $worldTypeName: $$tType).")
    }

    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def indexedAccessibilityRelationTPTPDef(typ: THF.Type): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_${serializeType(typ)}_type, type, mrel_${serializeType(typ)}: ${typ.pretty} > $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def polyIndexedAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: !>[T:$$tType]: (T > $worldTypeName > $worldTypeName > $$o)).")
    }

    private[this] def mglobalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mglobal_type, type, mglobal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mglobal_def, definition, mglobal = (^ [Phi: $worldTypeName > $$o]: ![W: $worldTypeName]: (Phi @ W)) ).")
      )
    }

    private[this] def mlocalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mactual_type, type, mactual: $worldTypeName)."),
        annotatedTHF(s"thf(mlocal_type, type, mlocal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mlocal_def, definition, mlocal = (^ [Phi: $worldTypeName > $$o]: (Phi @ mactual)) ).")
      )
    }

    private[this] def connectivesTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mnot_type, type , ( mnot: ($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mand_type, type , ( mand: ($worldTypeName>$$o)>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mor_type, type , ( mor: ($worldTypeName>$$o)>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mimplies_type, type , ( mimplies: ($worldTypeName>$$o)>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mequiv_type, type , ( mequiv: ($worldTypeName>$$o)>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mnot_def, definition , ( mnot = (^ [A:$worldTypeName>$$o,W:$worldTypeName] : ~(A@W))))."),
        annotatedTHF(s"thf(mand_def, definition , ( mand = (^ [A:$worldTypeName>$$o,B:$worldTypeName>$$o,W:$worldTypeName] : ( (A@W) & (B@W) ))))."),
        annotatedTHF(s"thf(mor_def, definition , ( mor = (^ [A:$worldTypeName>$$o,B:$worldTypeName>$$o,W:$worldTypeName] : ( (A@W) | (B@W) ))))."),
        annotatedTHF(s"thf(mimplies_def, definition , ( mimplies = (^ [A:$worldTypeName>$$o,B:$worldTypeName>$$o,W:$worldTypeName] : ( (A@W) => (B@W) ))))."),
        annotatedTHF(s"thf(mequiv_def, definition , ( mequiv = (^ [A:$worldTypeName>$$o,B:$worldTypeName>$$o,W:$worldTypeName] : ( (A@W) <=> (B@W) )))).")
      )
    }

    private[this] def simpleModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_type, type, mbox: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_type, type, mdia: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def indexedModalOperatorsTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_${serializeType(typ)}_type, type, mbox_${serializeType(typ)}: ${typ.pretty} > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_${serializeType(typ)}_def, definition, ( mbox_${serializeType(typ)} = (^ [R:${typ.pretty}, Phi:$worldTypeName>$$o,W:$worldTypeName]: ! [V:$worldTypeName]: ( (mrel_${serializeType(typ)} @ R @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_${serializeType(typ)}_type, type, mdia_${serializeType(typ)}: ${typ.pretty} > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_${serializeType(typ)}_def, definition, ( mdia_${serializeType(typ)} = (^ [R:${typ.pretty}, Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel_${serializeType(typ)} @ R @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def polyIndexedModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_type, type, mbox: !>[T:$$tType]: (T > ($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [T:$$tType, R:T, Phi:$worldTypeName>$$o, W:$worldTypeName]: ! [V:$worldTypeName]: ( (mrel @ T @ R @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_type, type, mdia: !>[T:$$tType]: (T > ($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [T:$$tType, R:T, Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ T @ R @ W @ V) & (Phi @ V) )))).")
      )
    }


    private[this] def indexedConstQuantifierTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_type, type, mforall_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_def, definition, mforall_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ! [X:${typ.pretty}]: (A @ X @ W)))."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_type, type, mexists_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_def, definition, mexists_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ? [X:${typ.pretty}]: (A @ X @ W))).")
      )
    }
    private[this] def indexedVaryQuantifierTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_type, type, mforall_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_def, definition, mforall_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ! [X:${typ.pretty}]: ((eiw_${serializeType(typ)} @ X @ W) => (A @ X @ W))))."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_type, type, mexists_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_def, definition, mexists_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ? [X:${typ.pretty}]: ((eiw_${serializeType(typ)} @ X @ W) & (A @ X @ W)))).")
      )
    }

    private[this] def polyIndexedVaryQuantifierTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mforall_vary_type, type, mforall_vary: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mforall_vary_def, definition, mforall_vary = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ! [X:T]: ((eiw @ T @ X @ W) => (A @ X @ W))))."),
        annotatedTHF(s"thf(mexists_vary_type, type, mexists_vary: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mexists_vary_def, definition, mexists_vary = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ? [X:T]: ((eiw @ T @ X @ W) & (A @ X @ W)))).")
      )
    }

    private[this] def polyIndexedConstQuantifierTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mforall_const_type, type, mforall_const: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mforall_const_def, definition, mforall_const = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ! [X:T]: (A @ X @ W)))."),
        annotatedTHF(s"thf(mexists_const_type, type, mexists_const: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mexists_const_def, definition, mexists_const = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ? [X:T]: (A @ X @ W))).")
      )
    }

    private[this] def indexedExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_type, type, eiw_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_nonempty, axiom, ![W:$worldTypeName]: ?[X:${typ.pretty}]: (eiw_${serializeType(typ)} @ X @ W) ).")
      )
    }
    private[this] def indexedCumulativeExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      if (isMultiModal) {
        modalOperators.keySet.map(mrelTy => annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel_${serializeType(mrelTy)} @ W @ V)) => (eiw_${serializeType(typ)} @ X @ V))).")).toSeq
      } else {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ W @ V)) => (eiw_${serializeType(typ)} @ X @ V))).")
        )
      }
    }
    private[this] def indexedDecreasingExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      if (isMultiModal) {
        modalOperators.keySet.map(mrelTy => annotatedTHF(s"thf(eiw_${serializeType(typ)}_decr, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel_${serializeType(mrelTy)} @ V @ W)) => (eiw_${serializeType(typ)} @ X @ V))).")).toSeq
      } else {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_decr, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ V @ W)) => (eiw_${serializeType(typ)} @ X @ V))).")
        )
      }
    }

    private[this] def indexedConverseBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      if (isMultiModal) {
        modalOperators.keySet.map { modalityTy =>
          val box = typeToBoxName(modalityTy)
          val formula = convertFormula(thf(s"($box @ I @ (![X:${typ.pretty}]: (P @ X))) => (![X:${typ.pretty}]: ($box @ I @ (P @ X)))")).pretty
          annotatedTHF(s"thf(cbf_${serializeType(typ)}_${serializeType(modalityTy)}, axiom, ![I: ${modalityTy.pretty}, P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula))).")
        }.toSeq
      } else {
        val formula = convertFormula(thf(s"($$box @ (![X:${typ.pretty}]: (P @ X))) => (![X:${typ.pretty}]: ($$box @ (P @ X)))")).pretty
        Seq(annotatedTHF(s"thf(cbf_${serializeType(typ)}, axiom, ![P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
      }
    }

    private[this] def indexedBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      if (isMultiModal) {
       modalOperators.keySet.map { modalityTy =>
         val box = typeToBoxName(modalityTy)
         val formula = convertFormula(thf(s"(![X:${typ.pretty}]: ($box @ I @ (P @ X))) => ($box @ I @ (![X:${typ.pretty}]: (P @ X)))")).pretty
         annotatedTHF(s"thf(bf_${serializeType(typ)}_${serializeType(modalityTy)}, axiom, ![I: ${modalityTy.pretty}, P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula))).")
       }.toSeq
      } else {
        val formula = convertFormula(thf(s"(![X:${typ.pretty}]: ($$box @ (P @ X))) => ($$box @ (![X:${typ.pretty}]: (P @ X)))")).pretty
        Seq(annotatedTHF(s"thf(bf_${serializeType(typ)}, axiom, ![P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
      }
    }

    private[this] def polyIndexedExistsInWorldTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_type, type, eiw: !>[T:$$tType]: (T > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(eiw_nonempty, axioms, ![T:$$tType, W:$worldTypeName]: ?[X:T]: (eiw @ T @ X @ W) ).")
      )
    }
    private[this] def polyIndexedCumulativeExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      if (isMultiModal) {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![T:$$tType, R:T, W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ T @ R @ W @ V)) => (eiw @ ${typ.pretty} @ X @ V))).")
        )
      } else {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ W @ V)) => (eiw @ ${typ.pretty} @ X @ V))).")
        )
      }
    }
    private[this] def polyIndexedDecreasingExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      if (isMultiModal) {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![T:$$tType, R:T, W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ T @ R @ V @ W)) => (eiw @ ${typ.pretty} @ X @ V))).")
        )
      } else {
        Seq(
          annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ V @ W)) => (eiw @ ${typ.pretty} @ X @ V))).")
        )
      }
    }

    lazy val semanticAxiomTable: Map[String, Option[TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.annotatedTHF
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> Some(annotatedTHF(
          s"thf(mrel_reflexive, axiom, ![W:$worldTypeName]: (mrel @ W @ W))."
          )),
        "$modal_axiom_B" -> Some(annotatedTHF(
          s"thf(mrel_symmetric, axiom, ![W:$worldTypeName, V:$worldTypeName]: ((mrel @ W @ V) => (mrel @ V @ W)))."
        )),
        "$modal_axiom_D" -> Some(annotatedTHF(
          s"thf(mrel_serial, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ W @ V))."
        )),
        "$modal_axiom_4" -> Some(annotatedTHF(
          s"thf(mrel_transitive, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ V) & (mrel @ V @ U)) => (mrel @ W @ U)))."
        )),
        "$modal_axiom_5" -> Some(annotatedTHF(
          s"thf(mrel_euclidean, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ U) & (mrel @ W @ V)) => (mrel @ U @ V)))."
        )),
        "$modal_axiom_C4" -> Some(annotatedTHF(
          s"thf(mrel_dense, axiom, ![W:$worldTypeName,U:$worldTypeName]: ((mrel @ W @ U) => (? [V:$worldTypeName]: ((mrel @ W @ V) & (mrel @ V @ U)))))."
        )),
        "$modal_axiom_CD" -> Some(annotatedTHF(
          s"thf(mrel_functional, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ U) & (mrel @ W @ V)) => (U = V)))."
        )),
        "$modal_axiom_S5U" -> Some(annotatedTHF(
          s"thf(mrel_universal, axiom, ![W:$worldTypeName,V:$worldTypeName]: (mrel @ W @ V))."
        ))
        // TODO: More axiom schemes
      )
    }
    lazy val syntacticAxiomTable: Map[String, Option[TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}

      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> {
          val formula = convertFormula(thf("($box @ Phi) => Phi")).pretty
          Some(annotatedTHF(
            s"thf(mrel_reflexive, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_B" -> {
          val formula = convertFormula(thf("Phi => ($box @ ($dia @ Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_symmetric, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_D" -> {
          val formula = convertFormula(thf("($box @ Phi) => ($dia @ Phi)")).pretty
          Some(annotatedTHF(
            s"thf(mrel_serial, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_4" -> {
          val formula = convertFormula(thf("($box @ Phi) => ($box @ ($box @ Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_transitive, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_5" -> {
          val formula = convertFormula(thf("($dia @ Phi) => ($box @ ($dia @ Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_euclidean, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_C4" -> {
          val formula = convertFormula(thf("($box @ ($box @ Phi)) => ($box @ Phi)")).pretty
          Some(annotatedTHF(
            s"thf(mrel_dense, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_CD" -> {
          val formula = convertFormula(thf("($dia @ Phi) => ($box @ Phi)")).pretty
          Some(annotatedTHF(
            s"thf(mrel_functional, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_GL" -> {
          val formula = convertFormula(thf("($box @ (($box @ Phi) => Phi)) => ($box @ Phi)")).pretty
          Some(annotatedTHF(
            s"thf(mrel_gl, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_GRZ" -> {
          val formula = convertFormula(thf("($box @ (($box @ (Phi => ($box @ Phi))) => Phi)) => Phi")).pretty
          Some(annotatedTHF(
            s"thf(mrel_grz, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_H" -> {
          val formula = convertFormula(thf("($box @ (($box @ Phi) => Psi)) | ($box @ (($box @ Psi) => Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_h, axiom, ![Phi:$worldTypeName>$$o, Psi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_M" -> {
          val formula = convertFormula(thf("($box @ ($dia @ Phi)) => ($dia @ ($box @ Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_m, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        },
        "$modal_axiom_G" -> {
          val formula = convertFormula(thf("($dia @ ($box @ Phi)) => ($box @ ($dia @ Phi))")).pretty
          Some(annotatedTHF(
            s"thf(mrel_g, axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
          ))
        }
      )
    }

    lazy val indexedSemanticAxiomTable: Map[String, Option[Function2[THF.Formula, THF.Type, TPTP.AnnotatedFormula]]] = {
      import modules.input.TPTPParser.annotatedTHF
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_reflexive', axiom, ![W:$worldTypeName]: (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ W))."
        )),
        "$modal_axiom_B" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_symmetric', axiom, ![W:$worldTypeName, V:$worldTypeName]: ((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V) => (mrel_${serializeType(typ)} @ ${idx.pretty} @ V @ W)))."
        )),
        "$modal_axiom_D" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_serial', axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V))."
        )),
        "$modal_axiom_4" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_transitive', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V) & (mrel_${serializeType(typ)} @ ${idx.pretty} @ V @ U)) => (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ U)))."
        )),
        "$modal_axiom_5" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_euclidean', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ U) & (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V)) => (mrel_${serializeType(typ)} @ ${idx.pretty} @ U @ V)))."
        )),
        "$modal_axiom_C4" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_dense', axiom, ![W:$worldTypeName,U:$worldTypeName]: ((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ U) => (? [V:$worldTypeName]: ((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V) & (mrel_${serializeType(typ)} @ ${idx.pretty} @ V @ U)))))."
        )),
        "$modal_axiom_CD" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_functional', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ U) & (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V)) => (U = V)))."
        )),
        "$modal_axiom_S5U" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${serializeType(typ)}_${idx.pretty}_universal', axiom, ![W:$worldTypeName,V:$worldTypeName]: (mrel_${serializeType(typ)} @ ${idx.pretty} @ W @ V))."
        ))
        // TODO: More axiom schemes
      )
    }
    private[this] def typeToBoxName(typ: THF.Type): String = {
      typ match {
        case THF.FunctionTerm("$i", Seq()) => "$box_i"
        case THF.FunctionTerm("$int", Seq()) => "$box_int"
        case _ => s"($$box_P @ ${typ.pretty})"
      }
    }
    private[this] def typeToDiaName(typ: THF.Type): String = {
      typ match {
        case THF.FunctionTerm("$i", Seq()) => "$dia_i"
        case THF.FunctionTerm("$int", Seq()) => "$dia_int"
        case _ => s"($$dia_P @ ${typ.pretty})"
      }
    }
    lazy val indexedSyntacticAxiomTable: Map[String, Option[Function2[THF.Formula, THF.Type, TPTP.AnnotatedFormula]]] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ Phi) => Phi")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_reflexive', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_B" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"Phi => ($box @ ${idx.pretty} @ ($dia @ ${idx.pretty} @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_symmetric', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_D" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ Phi) => ($dia @ ${idx.pretty} @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_serial', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_4" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ Phi) => ($box @ ${idx.pretty} @ ($box @ ${idx.pretty} @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_transitive', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_5" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"($dia @ ${idx.pretty} @ Phi) => ($box @ ${idx.pretty} @ ($dia @ ${idx.pretty} @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_euclidean', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_C4" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ ($box @ ${idx.pretty} @ Phi)) => ($box @ ${idx.pretty} @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_dense', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_CD" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"($dia @ ${idx.pretty} @ Phi) => ($box @ ${idx.pretty} @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_functional', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_GL" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ (($box @ ${idx.pretty} @ Phi) => Phi)) => ($box @ ${idx.pretty} @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_gl', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_GRZ" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ (($box @ ${idx.pretty} @ (Phi => ($box @ ${idx.pretty} @ Phi))) => Phi)) => Phi")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_grz', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_H" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ (($box @ ${idx.pretty} @ Phi) => Psi)) | ($box @ ${idx.pretty} @ (($box @ ${idx.pretty} @ Psi) => Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_h', axiom, ![Phi:$worldTypeName>$$o, Psi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_M" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"($box @ ${idx.pretty} @ ($dia @ ${idx.pretty} @ Phi)) => ($dia @ ${idx.pretty} @ ($box @ ${idx.pretty} @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_m', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_G" -> {
          Some((idx, typ) => {
            val box = typeToBoxName(typ)
            val dia = typeToDiaName(typ)
            val formula = convertFormula(thf(s"($dia @ ${idx.pretty} @ ($box @ ${idx.pretty} @ Phi)) => ($box @ ${idx.pretty} @ ($dia @ ${idx.pretty} @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${serializeType(typ)}_${idx.pretty}_g', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        }
      )
    }

    lazy val polyIndexedSemanticAxiomTable: Map[String, Option[Function2[THF.Formula, THF.Type, TPTP.AnnotatedFormula]]] = {
      import modules.input.TPTPParser.annotatedTHF
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_reflexive', axiom, ![W:$worldTypeName]: (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ W))."
        )),
        "$modal_axiom_B" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_symmetric', axiom, ![W:$worldTypeName, V:$worldTypeName]: ((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V) => (mrel @ ${typ.pretty} @ ${idx.pretty} @ V @ W)))."
        )),
        "$modal_axiom_D" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_serial', axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V))."
        )),
        "$modal_axiom_4" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_transitive', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V) & (mrel @ ${typ.pretty} @ ${idx.pretty} @ V @ U)) => (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ U)))."
        )),
        "$modal_axiom_5" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_euclidean', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ U) & (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V)) => (mrel @ ${typ.pretty} @ ${idx.pretty} @ U @ V)))."
        )),
        "$modal_axiom_C4" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_dense', axiom, ![W:$worldTypeName,U:$worldTypeName]: ((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ U) => (? [V:$worldTypeName]: ((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V) & (mrel @ ${typ.pretty} @ ${idx.pretty} @ V @ U)))))."
        )),
        "$modal_axiom_CD" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_functional', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ U) & (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V)) => (U = V)))."
        )),
        "$modal_axiom_S5U" -> Some((idx, typ) => annotatedTHF(
          s"thf('mrel_${idx.pretty}_universal', axiom, ![W:$worldTypeName,V:$worldTypeName]: (mrel @ ${typ.pretty} @ ${idx.pretty} @ W @ V))."
        ))
        // TODO: More axiom schemes
      )
    }
    lazy val polyIndexedSyntacticAxiomTable: Map[String, Option[Function2[THF.Formula, THF.Type, TPTP.AnnotatedFormula]]] = indexedSyntacticAxiomTable

    private def isModalSystemName(name: String): Boolean = name.startsWith("$modal_system_")
    lazy val modalSystemTable: Map[String, Seq[String]] = Map(
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
      "$modal_system_B" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_B"),
      "$modal_system_S4" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4"),
      "$modal_system_S5" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_5"),
      "$modal_system_S5U" -> Seq("$modal_axiom_S5U"),
      "$modal_system_K4W" -> Seq("$modal_axiom_K", "$modal_axiom_GL"),
      "$modal_system_4_1" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_H"),
      "$modal_system_4_2" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4", "$modal_axiom_M"),
      "$modal_system_4_3" -> Seq("$modal_axiom_K", "$modal_axiom_T", "$modal_axiom_4" ,"$modal_axiom_G"),
      "$modal_system_Grz" -> Seq("$modal_axiom_K", "$modal_axiom_Grz"),
      "$modal_system_GL" -> Seq("$modal_axiom_K", "$modal_axiom_GL")
    )

    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////

    private[this] def createState(spec: TPTP.AnnotatedFormula): Unit = {
      assert(spec.role == "logic")
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.:=, THF.FunctionTerm("$modal", Seq()),THF.Tuple(spec0))) =>
          spec0 foreach {
            case THF.BinaryFormula(THF.:=, THF.FunctionTerm(propertyName, Seq()), rhs) =>
              propertyName match {
                case "$constants" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$rigid") => state.setDefault(RIGIDITY, RIGIDITY_RIGID)
                    case Some("$flexible") => state.setDefault(RIGIDITY, RIGIDITY_FLEXIBLE)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, rigidity) =>
                    rigidity match {
                      case "$rigid" => state(RIGIDITY) += (name -> RIGIDITY_RIGID)
                      case "$flexible" => state(RIGIDITY) += (name -> RIGIDITY_FLEXIBLE)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$rigidity'")
                    }
                  }
                case "$quantification" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$constant") => state.setDefault(DOMAIN, DOMAIN_CONSTANT)
                    case Some("$varying") => state.setDefault(DOMAIN, DOMAIN_VARYING)
                    case Some("$cumulative") => state.setDefault(DOMAIN, DOMAIN_CUMULATIVE)
                    case Some("$decreasing") => state.setDefault(DOMAIN, DOMAIN_DECREASING)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, quantification) =>
                    quantification match {
                      case "$constant" => state(DOMAIN) += (name -> DOMAIN_CONSTANT)
                      case "$varying" => state(DOMAIN) += (name -> DOMAIN_VARYING)
                      case "$cumulative" => state(DOMAIN) += (name -> DOMAIN_CUMULATIVE)
                      case "$decreasing" => state(DOMAIN) += (name -> DOMAIN_DECREASING)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$quantification'")
                    }
                  }
                case "$consequence" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$local") => state.setDefault(CONSEQUENCE, CONSEQUENCE_LOCAL)
                    case Some("$global") => state.setDefault(CONSEQUENCE, CONSEQUENCE_GLOBAL)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, consequence) =>
                    consequence match {
                      case "$local" => state(CONSEQUENCE) += (name -> CONSEQUENCE_LOCAL)
                      case "$global" => state(CONSEQUENCE) += (name -> CONSEQUENCE_GLOBAL)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$consequence'")
                    }
                  }
                case "$modalities" => val (default, map) = parseListRHS(rhs)
                  if (default.nonEmpty) state.setDefault(MODALS, default)
                  map foreach { case (name, modalspec) =>
                    val realIndex = name match {
                      case THF.BinaryFormula(THF.App, THF.FunctionTerm(box, Seq()), index) if box.startsWith("$box") => index
                      case THF.FunctionTerm(box, Seq(index)) if box.startsWith("$box") => index
                      case _ => throw new EmbeddingException(s"Modality specification did not start with $$box ... := ...")
                    }
                    if (modalspec.nonEmpty) state(MODALS) += (realIndex -> modalspec)
                  }
                case _ => throw new EmbeddingException(s"Unknown modal logic semantics property '$propertyName'")
              }
            case s => throw new EmbeddingException(s"Malformed logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

}
