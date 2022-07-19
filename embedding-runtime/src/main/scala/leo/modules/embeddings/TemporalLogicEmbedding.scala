package leo
package modules
package embeddings

import datastructures.{FlexMap, TPTP}
import TPTP.{AnnotatedFormula, THF}

import java.util.logging.Logger
import scala.collection.mutable

object TemporalLogicEmbedding extends Embedding {
  object TemporalLogicEmbeddingOption extends Enumeration {
    // Hidden on purpose, to allow distinction between the object itself and its values.
    //    type ModalEmbeddingOption = Value
    final val MONOMORPHIC, POLYMORPHIC,
    MODALITIES_SEMANTICAL, MODALITIES_SYNTACTICAL,
    DOMAINS_SEMANTICAL, DOMAINS_SYNTACTICAL = Value
  }

  override type OptionType = TemporalLogicEmbeddingOption.type
  override final def embeddingParameter: TemporalLogicEmbeddingOption.type = TemporalLogicEmbeddingOption

  override final val name: String = "temporal_instant"
  override final def version: String = "1.0"

  private[this] final val defaultConstantSpec = "$rigid"
  private[this] final val defaultQuantificationSpec = "$constant"
  private[this] final val defaultModalitiesSpec = "$modal_system_K"
  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated = {
    import modules.input.TPTPParser.annotatedTHF
    val spec: mutable.StringBuilder = new mutable.StringBuilder
    spec.append("thf(logic_spec, logic, (")
    spec.append("$temporal_instant == [")
    spec.append("$constants == "); spec.append(specs.getOrElse("$constants", defaultConstantSpec)); spec.append(",")
    spec.append("$quantification == "); spec.append(specs.getOrElse("$quantification", defaultQuantificationSpec)); spec.append(",")
    spec.append("time == "); spec.append(specs.getOrElse("$modalities", defaultModalitiesSpec))
    spec.append("] )).")
    annotatedTHF(spec.toString)
  }

  override final def apply(problem: TPTP.Problem,
                           embeddingOptions: Set[TemporalLogicEmbeddingOption.Value]): TPTP.Problem =
    new TemporalLogicEmbeddingImpl(problem, embeddingOptions).apply()

  override final def apply(formulas: Seq[TPTP.AnnotatedFormula],
                           embeddingOptions: Set[TemporalLogicEmbeddingOption.Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class TemporalLogicEmbeddingImpl(problem: TPTP.Problem, embeddingOptions: Set[TemporalLogicEmbeddingOption.Value]) {
    import TemporalLogicEmbeddingOption._

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

    private final val MODALS = state.createKey[THF.Formula, Seq[THF.Formula]]()
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

      val (spec,sortFormulas,typeFormulas,definitionFormulas,otherFormulas) = splitInputByDifferentKindOfFormulas(formulas)
      createState(spec)
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      // new user types first (sort formulas), then our definitions, then all other formulas
      val result = sortFormulas ++ generatedMetaFormulas ++ convertedTypeFormulas ++ convertedDefinitionFormulas ++ convertedOtherFormulas
      // maybe add comments about warnings etc. in comments. If so, add them to very first formula in output.
      val updatedComments =
        if (result.isEmpty || warnings.isEmpty) problem.formulaComments
        else {
          val firstFormula = result.head
          val existingCommentsOfFirstFormula = problem.formulaComments.get(firstFormula.name)
          val newEntry = existingCommentsOfFirstFormula match {
            case Some(value) => warnings.toSeq.map(TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, _)) ++ value
            case None => warnings.toSeq.map(TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, _))
          }
          problem.formulaComments + (firstFormula.name -> newEntry)
        }

      TPTP.Problem(problem.includes, result, updatedComments)
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
      import TPTP.THF.{App, Eq, Neq}
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

        /* = and != are extra cases so we don't need to introduce defined symbols for them. Only works for first-order equality. */
        case THF.BinaryFormula(equalityLike, left, right) if Seq(Eq, Neq).contains(equalityLike) =>
          if (state.getDefault(DOMAIN).isDefined && state.getDefault(DOMAIN).get != DOMAIN_CONSTANT) {
            warnings.append(" WARNING: Equality used in modal logic problem with non-constant domains. Proceed with care, this may lead to strange results.")
            Logger.getGlobal.warning("Equality used in modal logic problem with non-constant domains. Proceed with care, this may lead to strange results.")
          }
          if (state.getDefault(RIGIDITY).isDefined && state.getDefault(RIGIDITY).get != RIGIDITY_RIGID) {
            warnings.append(" WARNING: Equality used in modal logic problem with flexible constants. Proceed with care, this may lead to strange results.")
            Logger.getGlobal.warning("Equality used in modal logic problem with flexible constants. Proceed with care, this may lead to strange results.")
          }
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          val body = THF.BinaryFormula(equalityLike, convertedLeft, convertedRight)
          THF.QuantifiedFormula(THF.^, Seq(("W", THF.FunctionTerm(worldTypeName, Seq.empty))), body)

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

    private[this] val inlineMifDef: THF.Formula =
      modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mimplies @ B @ A)")
    private[this] val inlineMniffDef: THF.Formula =
      modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mequiv @ A @ B))")
    private[this] val inlineMnorDef: THF.Formula =
      modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mor @ A @ B))")
    private[this] val inlineMnandDef: THF.Formula =
      modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mand @ A @ B))")

    private[this] def convertConnective(connective: TPTP.THF.Connective): THF.Formula = {
      connective match {
        case THF.~ => str2Fun("mnot")
        case THF.<=> => str2Fun("mequiv")
        case THF.Impl => str2Fun("mimplies")
        case THF.| => str2Fun("mor")
        case THF.& => str2Fun("mand")
        // other connectives of TPTP are encoded in terms of the above
        case THF.<= => inlineMifDef
        case THF.<~> => inlineMniffDef
        case THF.~| => inlineMnorDef
        case THF.~& => inlineMnandDef
        /// Non-classical connectives BEGIN
        // temporal operators
        case THF.NonclassicalLongOperator(name, parameters) =>
          name match {
            case "$henceforth" => parameters match {
              case Seq() => str2Fun("mbox_future")
              case _ => throw new EmbeddingException(s"No index is allowed in G operator, but parameters '${parameters.toString()}' was given.")
            }
            case "$future" => parameters match {
              case Seq() => str2Fun("mdia_future")
              case _ => throw new EmbeddingException(s"No index is allowed in F operator, but parameters '${parameters.toString()}' was given.")
            }
            case "$hitherto" => parameters match {
              case Seq() => str2Fun("mbox_past")
              case _ => throw new EmbeddingException(s"No index is allowed in H operator, but parameters '${parameters.toString()}' was given.")
            }
            case "$past" => parameters match {
              case Seq() => str2Fun("mdia_past")
              case _ => throw new EmbeddingException(s"No index is allowed in P operator, but parameters '${parameters.toString()}' was given.")
            }
            case _ => throw new EmbeddingException(s"Unknown connective name '$name'.")
          }
        /// Non-classical connectives END
        // Error cases
        case THF.App | THF.Eq | THF.Neq => throw new EmbeddingException(s"An unexpected error occurred, this is considered a bug. Please report it :-)")
        case THF.:= => throw new EmbeddingException(s"Unexpected assignment operator used as connective.")
        case THF.== => throw new EmbeddingException(s"Unexpected meta-logical identity operator used as connective.")
        case _ => throw new EmbeddingException(s"Unexpected operator or type constructor used as connective: '${connective.pretty}'")
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

    @inline private[this] def mglobal: THF.Formula = str2Fun("mglobal")
    @inline private[this] def mlocal: THF.Formula =  str2Fun("mlocal")

    private def convertTypeFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedTyping = TPTP.THF.Typing(symbol, convertType(typ))
          TPTP.THFAnnotated(name, role, convertedTyping, annotations)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Malformed type definition in formula '${formula.name}', aborting.")
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

    // For warnings that should go inside the output file
    private[this] val warnings: mutable.Buffer[String] = mutable.Buffer.empty

    private[this] var localFormulaExists = false
    private[this] var globalFormulaExists = false


//    private[this] def escapeModalIndex(index: THF.Formula): THF.FunctionTerm = index match {
//      case THF.FunctionTerm(name, args) => THF.FunctionTerm(s"#$name", args)
//      case THF.NumberTerm(TPTP.Integer(value)) => THF.FunctionTerm(s"#$value", Seq.empty)
//      case _ => throw new EmbeddingException(s"Unsupported index '${index.pretty}'")
//    }

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
      result.append(simpleAccessibilityRelationTPTPDef())
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
      result.appendAll(simpleModalOperatorsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Give mrel properties (sem/syn)
      // write used properties and assign (if semantical)
      // or write syntactical axioms (if syntactical)
      val modalSystem = state.getDefault(MODALS)
      modalSystem match {
        case Some(value) =>
          val axiomNames = value
          val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) semanticAxiomTable else syntacticAxiomTable
          val modalAxioms = axiomNames.flatMap(axiomTable).toSet
          result.appendAll(modalAxioms)
        case None => throw new EmbeddingException(s"No semantics for modal operators specified, embedding not possible.")
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
        annotatedTHF(s"thf(mbox_future_type, type, mbox_future: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_future_def, definition, ( mbox_future = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_future_type, type, mdia_future: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_future_def, definition, ( mdia_future = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ W @ V) & (Phi @ V) ))))."),
        annotatedTHF(s"thf(mbox_past_type, type, mbox_past: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_past_def, definition, ( mbox_past = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel @ V @ W) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_past_type, type, mdia_past: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_past_def, definition, ( mdia_past = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ V @ W) & (Phi @ V) )))).")
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
      Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ W @ V)) => (eiw_${serializeType(typ)} @ X @ V)))."))
    }
    private[this] def indexedDecreasingExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(annotatedTHF(s"thf(eiw_${serializeType(typ)}_decr, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw_${serializeType(typ)} @ X @ W) & (mrel @ V @ W)) => (eiw_${serializeType(typ)} @ X @ V)))."))
    }

    private[this] def indexedConverseBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      val formula = convertFormula(thf(s"($$box @ (![X:${typ.pretty}]: (P @ X))) => (![X:${typ.pretty}]: ($$box @ (P @ X)))")).pretty
      Seq(annotatedTHF(s"thf(cbf_${serializeType(typ)}, axiom, ![P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
    }

    private[this] def indexedBarcanFormulaTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}
      val formula = convertFormula(thf(s"(![X:${typ.pretty}]: ($$box @ (P @ X))) => ($$box @ (![X:${typ.pretty}]: (P @ X)))")).pretty
      Seq(annotatedTHF(s"thf(bf_${serializeType(typ)}, axiom, ![P:${typ.pretty} > ($worldTypeName>$$o)]: (mglobal @ ($formula)))."))
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
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ W @ V)) => (eiw @ ${typ.pretty} @ X @ V))).")
      )
    }
    private[this] def polyIndexedDecreasingExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, X:${typ.pretty}]: (((eiw @ ${typ.pretty} @ X @ W) & (mrel @ V @ W)) => (eiw @ ${typ.pretty} @ X @ V))).")
      )
    }

    lazy val semanticAxiomTable: Map[TPTP.THF.Formula, Option[TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.annotatedTHF
      Map(
        TPTP.THF.FunctionTerm("$reflexivity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_reflexive, axiom, ![W:$worldTypeName]: (mrel @ W @ W))."
        )),
        TPTP.THF.FunctionTerm("$irreflexivity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_irreflexive, axiom, ![W:$worldTypeName]: (~(mrel @ W @ W)))."
        )),
        TPTP.THF.FunctionTerm("$transitivity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_transitive, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ V) & (mrel @ V @ U)) => (mrel @ W @ U)))."
        )),
        TPTP.THF.FunctionTerm("$asymmetry", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_asymmetry, axiom, ![W:$worldTypeName,V:$worldTypeName]: (~((mrel @ W @ V) & (mrel @ V @ W))))."
        )),
        TPTP.THF.FunctionTerm("$anti_symmetry", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_antisymmetry, axiom, ![W:$worldTypeName,V:$worldTypeName]: (((mrel @ W @ V) & (mrel @ V @ W)) => (V = W)))."
        )),
        TPTP.THF.FunctionTerm("$linearity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_linearity, axiom, ![W:$worldTypeName,V:$worldTypeName]: ((W = V) | (mrel @ W @ V) | (mrel @ V @ W)))."
        )),
        TPTP.THF.FunctionTerm("$forward_linearity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_forward_linearity, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ U @ W) & (mrel @ U @ V)) => ((W = V) | (mrel @ W @ V) | (mrel @ V @ W))))."
        )),
        TPTP.THF.FunctionTerm("$backward_linearity", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_backward_linearity, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ U) & (mrel @ V @ U)) => ((W = V) | (mrel @ W @ V) | (mrel @ V @ W))))."
        )),
        TPTP.THF.FunctionTerm("$beginning", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_serial_past, axiom, ![W:$worldTypeName]: (~ (?[V:$worldTypeName]: (mrel @ V @ W))))."
        )),
        TPTP.THF.FunctionTerm("$end", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_serial_future, axiom, ![W:$worldTypeName]: (~ (?[V:$worldTypeName]: (mrel @ W @ V))))."
        )),
        TPTP.THF.FunctionTerm("$no_beginning", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_serial_past, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ V @ W))."
        )),
        TPTP.THF.FunctionTerm("$no_end", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_serial_future, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ W @ V))."
        )),
        TPTP.THF.FunctionTerm("$density", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_density, axiom, ![W:$worldTypeName,V:$worldTypeName]: ((mrel @ W @ V) => (?[U:$worldTypeName]: ((mrel @ W @ U) & (mrel @ U @ V))) ))."
        )),
        TPTP.THF.FunctionTerm("$forward_discreteness", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_forward_discreteness, axiom, ![W:$worldTypeName,V:$worldTypeName]: ((mrel @ W @ V) => (?[U:$worldTypeName]: ((mrel @ W @ U) & (mrel @ U @ V) & ~(?[Z:$worldTypeName]: ((mrel @ W @ Z) & (mrel @ Z @ U)))))) )."
        )),
        TPTP.THF.FunctionTerm("$backward_discreteness", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_backward_discreteness, axiom, ![W:$worldTypeName,V:$worldTypeName]: ((mrel @ V @ W) => (?[U:$worldTypeName]: ((mrel @ U @ W) & (mrel @ V @ U) & ~(?[Z:$worldTypeName]: ((mrel @ Z @ W) & (mrel @ U @ Z)))))) )."
        )),
        TPTP.THF.FunctionTerm("$modal_axiom_K", Seq.empty) -> None,
        TPTP.THF.FunctionTerm("$modal_axiom_T", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_reflexive_t, axiom, ![W:$worldTypeName]: (mrel @ W @ W))."
        )),
        TPTP.THF.FunctionTerm("$modal_axiom_B", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_symmetric_b, axiom, ![W:$worldTypeName, V:$worldTypeName]: ((mrel @ W @ V) => (mrel @ V @ W)))."
        )),
        TPTP.THF.FunctionTerm("$modal_axiom_D", Seq(TPTP.THF.FunctionTerm("future", Seq.empty))) ->
          Some(annotatedTHF(
            s"thf(mrel_serial_future_d, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ W @ V))."
          )),
        TPTP.THF.FunctionTerm("$modal_axiom_D", Seq(TPTP.THF.FunctionTerm("past", Seq.empty))) ->
          Some(annotatedTHF(
            s"thf(mrel_serial_past_d, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (mrel @ V @ W))."
          )),
        TPTP.THF.FunctionTerm("$modal_axiom_4", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_transitive_4, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ V) & (mrel @ V @ U)) => (mrel @ W @ U)))."
        )),
        TPTP.THF.FunctionTerm("$modal_axiom_5", Seq.empty) -> Some(annotatedTHF(
          s"thf(mrel_euclidean_5, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((mrel @ W @ U) & (mrel @ W @ V)) => (mrel @ U @ V)))."
        ))
      )
    }
    lazy val syntacticAxiomTable: Map[TPTP.THF.Formula, Option[TPTP.AnnotatedFormula]] = {
      import modules.input.TPTPParser.{annotatedTHF, thf}

      Map(
        TPTP.THF.FunctionTerm("$modal_axiom_K", Seq.empty) -> None // TODO
      )
    }

    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////

    private[this] def createState(spec: TPTP.AnnotatedFormula): Unit = {
      assert(spec.role == "logic")
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm("$temporal_instant", Seq()),THF.Tuple(spec0))) =>
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
                case "$modalities" => val (default, map) = parseListRHSNew(rhs)
                  if (default.nonEmpty && map.isEmpty) {
                      state.setDefault(MODALS, default)
                  } else throw new EmbeddingException(s"Unspecified modality or ill-specified modality..")
                case _ => throw new EmbeddingException(s"Unknown modal logic semantics property '$propertyName'")
              }
            case s => throw new EmbeddingException(s"Malformed logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

}
