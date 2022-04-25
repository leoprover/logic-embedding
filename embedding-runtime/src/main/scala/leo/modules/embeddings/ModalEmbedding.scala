package leo
package modules
package embeddings

import datastructures.{FlexMap, TPTP}
import TPTP.{AnnotatedFormula, THF}

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
  override final def version: String = "1.5.2"

  private[this] final val defaultConstantSpec = "$rigid"
  private[this] final val defaultQuantificationSpec = "$constant"
  private[this] final val defaultModalitiesSpec = "$modal_system_K"
  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated = {
    import modules.input.TPTPParser.annotatedTHF
    val spec: StringBuilder = new StringBuilder
    spec.append("thf(logic_spec, logic, (")
    spec.append("$modal == [")
    spec.append("$constants == "); spec.append(specs.getOrElse("$constants", defaultConstantSpec)); spec.append(",")
    spec.append("$quantification == "); spec.append(specs.getOrElse("$quantification", defaultQuantificationSpec)); spec.append(",")
    spec.append("$modalities == "); spec.append(specs.getOrElse("$modalities", defaultModalitiesSpec))
    spec.append("] )).")
    annotatedTHF(spec.toString)
  }

  override final def apply(problem: TPTP.Problem,
                  embeddingOptions: Set[ModalEmbeddingOption.Value]): TPTP.Problem =
    new ModalEmbeddingImpl(problem, embeddingOptions).apply()

  override final def apply(formulas: Seq[TPTP.AnnotatedFormula],
                           embeddingOptions: Set[ModalEmbeddingOption.Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class ModalEmbeddingImpl(problem: TPTP.Problem, embeddingOptions: Set[ModalEmbeddingOption.Value]) {
    import ModalEmbeddingOption._

    ///////////////////////////////////////////////////////////////////
    private final val state = FlexMap.apply()

    // Semantics dimensions
    private final val RIGIDITY_RIGID = true
    private final val RIGIDITY_FLEXIBLE = false
    private final val RIGIDITY = state.createKey[String, Boolean]()
    // Standard TPTP-defined rigid constants/designators
    state(RIGIDITY) ++= Seq("$true" -> RIGIDITY_RIGID, "$false" -> RIGIDITY_RIGID,
      "$less" -> RIGIDITY_RIGID, "$lesseq" -> RIGIDITY_RIGID,
      "$greater" -> RIGIDITY_RIGID, "$greatereq" -> RIGIDITY_RIGID)

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

    def apply(): TPTP.Problem = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val formulas = problemTHF.formulas
      val (spec, properFormulas) = splitInput(formulas)
      createState(spec)
      val (typeFormulas, nonTypeFormulas) = properFormulas.partition(_.role == "type")
      val (definitionFormulas, otherFormulas) = nonTypeFormulas.partition(_.role == "definition")
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      val result = generatedMetaFormulas ++ convertedTypeFormulas ++ convertedDefinitionFormulas ++ convertedOtherFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }

    def convertDefinitionFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), body)), annotations) =>
          TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), convertFormula(body))), annotations)
        case _ => convertAnnotatedFormula(formula)
      }
    }

    def convertAnnotatedFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      import leo.modules.tptputils._
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Logical(formula), annotations) =>
          val convertedFormula0 = convertFormula(formula)
          val convertedFormula = role match {
            case "hypothesis" | "conjecture" => // assumed to be local
              localFormulaExists = true
              THF.BinaryFormula(THF.App, mlocal, convertedFormula0)
            case _ if isSimpleRole(role) => // everything else is assumed to be global
              globalFormulaExists = true
              THF.BinaryFormula(THF.App, mglobal, convertedFormula0)
            case _ => // role with subroles, check whether a subrole specified $local or $global explicitly
              getSubrole(role).get match {
                case "local" =>
                  localFormulaExists = true
                  THF.BinaryFormula(THF.App, mlocal, convertedFormula0)
                case "global" =>
                  globalFormulaExists = true
                  THF.BinaryFormula(THF.App, mglobal, convertedFormula0)
                case x => throw new EmbeddingException(s"Unknown subrole '$x' in conversion of formula '$name'. ")
              }
          }
          // Strip $local, $global etc. role contents from role (as classical ATPs cannot deal with it)
          // And normalize hypothesis to axiom.
          val updatedRole = toSimpleRole(role) match {
            case "hypothesis" => "axiom"
            case r => r
          }
          TPTP.THFAnnotated(name, updatedRole, TPTP.THF.Logical(convertedFormula), annotations)
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
        case THF.FunctionTerm(f, Seq()) if tptpDefinedNullaryPredicateSymbols.contains(f) =>
          thf(s"^[W: $worldTypeName]: $f")

        // Unary: $is_int, $is_rat, etc., see discussion below
        case THF.BinaryFormula(App, THF.FunctionTerm(f, Seq()), right)
          if tptpDefinedUnaryArithmeticPredicateSymbols.contains(f) =>

          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          thf(s"^[W:$worldTypeName]: ($f @ (${convertedRight.pretty}))")

        // Binary: $less, $lesseq, $greater, $greatereq -> (^[W:mworld]: ...) as they are rigid constants.
          // This will not work for partially applied function expressions, e.g. (f @ $greater).
          // but the embedding will be much more complicated when we support this, as $greater and friends
          // are ad-hoc polymorphic and would need to be embedded to ^[X:T, Y:T, W:mworld]: ($greater @ X @ Y)
          // but we don't know what T is supposed to be. And just embedding $greater to ^[W:mworld]: $greater
          // will not be type-correct.
        case THF.BinaryFormula(App, THF.BinaryFormula(App, THF.FunctionTerm(f, Seq()), left), right)
          if tptpDefinedBinaryArithmeticPredicateSymbols.contains(f) =>

          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          thf(s"^[W:$worldTypeName]: ($f @ (${convertedLeft.pretty}) @ (${convertedRight.pretty}))")

        /* ######################################### */
        /* Standard cases: Recurse embedding. */
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertFormula)
          THF.FunctionTerm(f, convertedArgs)

        case THF.QuantifiedFormula(THF.^, variableList, body) =>
          val convertedBody = convertFormula(body)
          val convertedVariableList = variableList.map {case (name, ty) => (name, convertType(ty))}
          THF.QuantifiedFormula(THF.^, convertedVariableList, convertedBody)

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

        case THF.ConditionalTerm(condition, thn, els) => // TODO: Will only work for $ite where the body (then and else)
                                                         // are formulas
          val convertedCondition: TPTP.THF.Formula = convertFormula(condition)
          val convertedThn: TPTP.THF.Formula = convertFormula(thn)
          val convertedEls: TPTP.THF.Formula = convertFormula(els)
          localFormulaExists = true
          val conditionalBody = THF.ConditionalTerm(
            THF.BinaryFormula(THF.App, convertedCondition, THF.Variable("ITEWORLD")),
            THF.BinaryFormula(THF.App, convertedThn, THF.Variable("ITEWORLD")),
            THF.BinaryFormula(THF.App, convertedEls, THF.Variable("ITEWORLD")))
          THF.QuantifiedFormula(THF.^, Seq(("ITEWORLD", THF.FunctionTerm(worldTypeName, Seq.empty))), conditionalBody)


        case THF.LetTerm(typing, binding, body) => // This will probably change as the parse tree of LetTerms will still change.
          val convertedTyping: Map[String, TPTP.THF.Type] = typing.map(a => (a._1, convertType(a._2)))
          val convertedBinding: Seq[(TPTP.THF.Formula, TPTP.THF.Formula)] = binding.map(a => (convertFormula(a._1), convertFormula(a._2)))
          val convertedBody = convertFormula(body)
          THF.LetTerm(convertedTyping, convertedBinding, convertedBody)
        case THF.DistinctObject(_) => formula
        case THF.NumberTerm(_) => formula
      }
    }

    private[this] def convertConnective(connective: TPTP.THF.Connective): THF.Formula = {
      connective match {
        case THF.~ => str2Fun("mnot")
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
          case Some(index0) => mboxIndexed(index0)
          case None => str2Fun("mbox")
        }
        // Diamond operator
        case THF.NonclassicalDiamond(index) => index match {
          case Some(index0) => mdiaIndexed(index0)
          case None => str2Fun("mdia")
        }
        case THF.NonclassicalLongOperator(name, parameters) =>
          name match {
            case "$box" | "$necessary" | "$obligatory" | "$knows" => parameters match {
              case Seq() => str2Fun("mbox")
              case Seq(Left(index0)) => mboxIndexed(index0)
              case _ => throw new EmbeddingException(s"Only up to one index is allowed in box operator, but parameters '${parameters.toString()}' was given.")
            }
            case "$dia" | "$possible" | "$permissible" => parameters match {
              case Seq() => str2Fun("mdia")
              case Seq(Left(index0)) => mdiaIndexed(index0)
              case _ => throw new EmbeddingException(s"Only up to one index is allowed in diamond operator, but parameters '${parameters.toString()}' was given.")
            }
            case _ => throw new EmbeddingException(s"Unknown connective name '$name'.")
          }

        /// Non-classical connectives END
        // Error cases
        case THF.Eq | THF.Neq => throw new EmbeddingException(s"Equality and inequality are not supported (due to inclarities with equality in modal logic). Please consider axiomatizing your own equality predicate in the problem.")
        case THF.App => throw new EmbeddingException(s"An unexpected error occurred, this is considered a bug. Please report it :-)")
        case THF.:= => throw new EmbeddingException(s"Unexpected assignment operator used as connective.")
        case THF.== => throw new EmbeddingException(s"Unexpected meta-logical identity operator used as connective.")
        case _ => throw new EmbeddingException(s"Unexpected type constructor used as connective: '${connective.pretty}'")
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
        case THF.@+ => "mchoice"
        case THF.@- => "mdescription"
        case _ => throw new EmbeddingException(s"Unexpected quantifier used as term quantifier: '${quantifier.pretty}'")
      }
      THF.FunctionTerm(name, Seq.empty)
    }

    @inline private[this] def mbox: THF.Formula = str2Fun("mbox")
    private[this] def mboxIndexed(index: THF.Formula): THF.Formula = {
      THF.BinaryFormula(THF.App, mbox, multiModal(index))
    }
    @inline private[this] def mdia: THF.Formula = str2Fun("mdia")
    private[this] def mdiaIndexed(index: THF.Formula): THF.Formula = {
      THF.BinaryFormula(THF.App, mdia, multiModal(index))
    }

    @inline private[this] def mglobal: THF.Formula = str2Fun("mglobal")
    @inline private[this] def mlocal: THF.Formula =  str2Fun("mlocal")

    private def convertTypeFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedTyping = TPTP.THF.Typing(symbol, convertType(typ))
//          typedSymbolsInOriginalProblem += (symbol -> typ)
          TPTP.THFAnnotated(name, role, convertedTyping, annotations)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertType)
          if (f == "$o") THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), THF.FunctionTerm(f, convertedArgs))
          else THF.FunctionTerm(f, convertedArgs)

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

    private[this] var localFormulaExists = false
    private[this] var globalFormulaExists = false

    private[this] val modalOperators: mutable.Set[THF.FunctionTerm] = mutable.Set.empty
    private[this] def isMultiModal: Boolean = modalOperators.nonEmpty
    private[this] def multiModal(index: THF.Formula): THF.FunctionTerm = {
      val index0 = escapeModalIndex(index)
      modalOperators += index0
      index0
    }
    private[this] def escapeModalIndex(index: THF.Formula): THF.FunctionTerm = index match {
        case THF.FunctionTerm(name, args) => THF.FunctionTerm(s"#$name", args)
        case THF.NumberTerm(TPTP.Integer(value)) => THF.FunctionTerm(s"#$value", Seq.empty)
        case _ => throw new EmbeddingException(s"Unsupported index '${index.pretty}'")
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
      // Then: Introduce index type (if multi-modal)
      if (isMultiModal) {
        result.append(indexTypeTPTPDef())
      }
      /////////////////////////////////////////////////////////////
      // Then: Introduce mrel (as relation or as collection of relations)
      if (isMultiModal) result.append(indexedAccessibilityRelationTPTPDef())
      else result.append(simpleAccessibilityRelationTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Introduce index values (if multimodal)
      if (isMultiModal) {
        modalOperators.foreach { index =>
          result.append(indexTPTPDef(index))
        }
      }
      /////////////////////////////////////////////////////////////
      // Then: Define mglobal/mlocal
      if (localFormulaExists) {
        result.appendAll(mlocalTPTPDef())
      }
      if (globalFormulaExists ||
        modalityEmbeddingType == MODALITY_EMBEDDING_SYNTACTICAL ||  // We use mglobal for those meta-definitions
        domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL) {     // so introduce mglobal also if there is no global
        result.appendAll(mglobalTPTPDef())                          // object-level formula
      }
      /////////////////////////////////////////////////////////////
      // Then: Define connectives
      result.appendAll(connectivesTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define modal operators
      if (isMultiModal) result.appendAll(indexedModalOperatorsTPTPDef())
      else result.appendAll(simpleModalOperatorsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Give mrel properties (sem/syn)
      // write used properties and assign (if semantical)
      // or write syntactical axioms (if syntactical)
      if (isMultiModal) {
        val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) indexedSemanticAxiomTable else indexedSyntacticAxiomTable
        modalOperators foreach { index =>
          val modalSystem = state(MODALS).apply(index)
          val axiomNames = if (isModalSystemName(modalSystem.head)) modalSystemTable(modalSystem.head) else modalSystem
          axiomNames foreach { ax =>
            val axiom = axiomTable.apply(ax)
            axiom.foreach { f =>
              val res = f(index)
              result.append(res)
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
    @inline private[this] def indexTypeName: String = "mindex"

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($worldTypeName, type, $worldTypeName: $$tType).")
    }
    private[this] def indexTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($indexTypeName, type, $indexTypeName: $$tType).")
    }

    private[this] def indexTPTPDef(index: THF.FunctionTerm): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      val name = s"${unescapeTPTPName(index.pretty)}_type"
      annotatedTHF(s"thf(${escapeName(name)}, type, ${index.pretty}: $indexTypeName).")
    }

    private[this] def unescapeTPTPName(name: String): String = {
      if (name.startsWith("'") && name.endsWith("'")) {
        name.tail.init
      } else name
    }
    private def escapeName(name: String): String = {
      val integerRegex = "^[+-]?[\\d]+$"
      if (name.matches(integerRegex)) name else escapeAtomicWord(name)
    }
    private def escapeAtomicWord(word: String): String = {
      val simpleLowerWordRegex = "^[a-z][a-zA-Z\\d_]*$"
      if (word.matches(simpleLowerWordRegex)) word
      else s"'${word.replace("\\","\\\\").replace("'", "\\'")}'"
    }

    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def indexedAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $indexTypeName > $worldTypeName > $worldTypeName > $$o).")
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

    private[this] def indexedModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_type, type, mbox: $indexTypeName > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [R:$indexTypeName, Phi:$worldTypeName>$$o,W:$worldTypeName]: ! [V:$worldTypeName]: ( (mrel @ R @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_type, type, mdia: $indexTypeName > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [R:$indexTypeName, Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ R @ W @ V) & (Phi @ V) )))).")
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
      if (isMultiModal) Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![Index:$indexTypeName, W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ Index @ W @ V)) => (eiw_${serializeType(typ)} @ X @ V)))."))
      else Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ W @ V)) => (eiw_${serializeType(typ)} @ X @ V)))."))
    }
    private[this] def indexedDecreasingExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      if (isMultiModal) Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_decr, axiom, ![Index: $indexTypeName, W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ Index @ V @ W)) => (eiw_${serializeType(typ)} @ X @ V)))."))
      else Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_decr, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ V @ W)) => (eiw_${serializeType(typ)} @ X @ V)))."))
    }

    private[this] def indexedConverseBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      if (isMultiModal) {
          val box = "[#I]"
          val formula = convertFormula(thf(s"($box @ (![X:${typ.pretty}]: (P @ X))) => (![X:${typ.pretty}]: ($box @ (P @ X)))")).pretty
          Seq(annotatedTHF(s"thf(cbf_${serializeType(typ)}, axiom, ![I: $indexTypeName, P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
      } else {
        val formula = convertFormula(thf(s"($$box @ (![X:${typ.pretty}]: (P @ X))) => (![X:${typ.pretty}]: ($$box @ (P @ X)))")).pretty
        Seq(annotatedTHF(s"thf(cbf_${serializeType(typ)}, axiom, ![P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
      }
    }

    private[this] def indexedBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      if (isMultiModal) {
         val box = "[#I]"
         val formula = convertFormula(thf(s"(![X:${typ.pretty}]: ($box @ (P @ X))) => ($box @ (![X:${typ.pretty}]: (P @ X)))")).pretty
         Seq(annotatedTHF(s"thf(bf_${serializeType(typ)}, axiom, ![I: $indexTypeName, P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
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

    lazy val indexedSyntacticAxiomTable: Map[String, Option[THF.Formula => TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ Phi) => Phi")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_reflexive', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_B" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"Phi => ($box @ ($dia @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_symmetric', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_D" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"($box @ Phi) => ($dia @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_serial', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_4" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ Phi) => ($box @ ($box @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_transitive', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_5" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"($dia @ Phi) => ($box @ ($dia @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_euclidean', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_C4" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ ($box @ Phi)) => ($box @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_dense', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_CD" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"($dia @ Phi) => ($box @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_functional', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_GL" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ (($box @ Phi) => Phi)) => ($box @ Phi)")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_gl', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_GRZ" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ (($box @ (Phi => ($box @ Phi))) => Phi)) => Phi")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_grz', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_H" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val formula = convertFormula(thf(s"($box @ (($box @ Phi) => Psi)) | ($box @ (($box @ Psi) => Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_h', axiom, ![Phi:$worldTypeName>$$o, Psi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_M" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"($box @ ($dia @ Phi)) => ($dia @ ($box @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_m', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        },
        "$modal_axiom_G" -> {
          Some(idx => {
            val box = s"[#${idx.pretty}]"
            val dia = s"<#${idx.pretty}>"
            val formula = convertFormula(thf(s"($dia @ ($box @ Phi)) => ($box @ ($dia @ Phi))")).pretty
            annotatedTHF(
              s"thf('mrel_${unescapeTPTPName(idx.pretty)}_g', axiom, ![Phi:$worldTypeName>$$o]: (mglobal @ ($formula)))."
            )
          })
        }
      )
    }

    lazy val indexedSemanticAxiomTable: Map[String, Option[THF.Formula => TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.annotatedTHF
      Map(
        "$modal_axiom_K" -> None,
        "$modal_axiom_T" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_reflexive', axiom, ![W:$worldTypeName]: (mrel @ ${idx.pretty} @ W @ W))."
        )),
        "$modal_axiom_B" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_symmetric', axiom, ![W:$worldTypeName, V:$worldTypeName]: ((mrel @ ${idx.pretty} @ W @ V) => (mrel @ ${idx.pretty} @ V @ W)))."
        )),
        "$modal_axiom_D" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_serial', axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ ${idx.pretty} @ W @ V))."
        )),
        "$modal_axiom_4" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_transitive', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${idx.pretty} @ W @ V) & (mrel @ ${idx.pretty} @ V @ U)) => (mrel @ ${idx.pretty} @ W @ U)))."
        )),
        "$modal_axiom_5" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_euclidean', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${idx.pretty} @ W @ U) & (mrel @ ${idx.pretty} @ W @ V)) => (mrel @ ${idx.pretty} @ U @ V)))."
        )),
        "$modal_axiom_C4" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_dense', axiom, ![W:$worldTypeName,U:$worldTypeName]: ((mrel @ ${idx.pretty} @ W @ U) => (? [V:$worldTypeName]: ((mrel @ ${idx.pretty} @ W @ V) & (mrel @ ${idx.pretty} @ V @ U)))))."
        )),
        "$modal_axiom_CD" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_functional', axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ ${idx.pretty} @ W @ U) & (mrel @ ${idx.pretty} @ W @ V)) => (U = V)))."
        )),
        "$modal_axiom_S5U" -> Some(idx => annotatedTHF(
          s"thf('mrel_${unescapeTPTPName(idx.pretty)}_universal', axiom, ![W:$worldTypeName,V:$worldTypeName]: (mrel @ ${idx.pretty} @ W @ V))."
        ))
        // TODO: More axiom schemes
      )
    }

    private def isModalAxiomName(name: String): Boolean = name.startsWith("$modal_axiom_")
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
        case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(name, Seq()),THF.Tuple(spec0))) if Seq("$modal", "$alethic_modal", "$deontic_modal", "$epistemic_modal") contains name =>
          spec0 foreach {
            case THF.BinaryFormula(THF.==, THF.FunctionTerm(propertyName, Seq()), rhs) =>
              propertyName match {
                case "$constants" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$rigid") => state.setDefault(RIGIDITY, RIGIDITY_RIGID)
                    case Some("$flexible") => state.setDefault(RIGIDITY, RIGIDITY_FLEXIBLE)
                      throw new EmbeddingException("Unsupported modal logic semantics: flexible constants not yet supported.") // TODO
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, rigidity) =>
                    rigidity match {
                      case "$rigid" => state(RIGIDITY) += (name -> RIGIDITY_RIGID)
                      case "$flexible" => state(RIGIDITY) += (name -> RIGIDITY_FLEXIBLE)
                        throw new EmbeddingException("Unsupported modal logic semantics: flexible constants not yet supported.") // TODO
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
                case "$modalities" => val (default, map) = parseListRHS(rhs)
                  if (default.nonEmpty) {
                    if (default.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec)))
                      state.setDefault(MODALS, default)
                    else throw new EmbeddingException(s"Unknown modality specification: ${default.mkString("[",",", "]")}")
                  }
                  map foreach { case (lhs, modalspec) =>
                    val index0 = lhs match {
                      case THF.ConnectiveTerm(THF.NonclassicalBox(Some(index))) => index
                      case THF.ConnectiveTerm(THF.NonclassicalLongOperator(cname, Seq(Left(index))))
                       if Seq("$box", "$necessary" , "$obligatory" , "$knows").contains(cname) => index
                      case _ => throw new EmbeddingException(s"Modality specification did not start with '[#idx] == ...' or '{#box(#idx)} == ...'.")
                    }
                    val index = escapeModalIndex(index0)
                    if (modalspec.nonEmpty) {
                      if (modalspec.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec)))
                        state(MODALS) += (index -> modalspec)
                      else throw new EmbeddingException(s"Unknown modality specification: ${modalspec.mkString("[",",", "]")}")
                    }
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
