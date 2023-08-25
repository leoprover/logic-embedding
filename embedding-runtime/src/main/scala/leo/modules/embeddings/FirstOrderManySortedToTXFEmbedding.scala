package leo
package modules
package embeddings

import datastructures.TPTP
import TPTP.{AnnotatedFormula, TFF, TFFAnnotated}
import leo.modules.input.TPTPParser.annotatedTFF

import scala.annotation.unused

object FirstOrderManySortedToTXFEmbedding extends Embedding {

  object FOMLToTXFEmbeddingParameter extends Enumeration {
    // Hidden on purpose, to allow distinction between the object itself and its values.
    //    type FOMLToTXFEmbeddingParameter = Value
    final val POLYMORPHIC, LOCALEXTENSION, EMPTYDOMAINS = Value
  }
  override type OptionType = FOMLToTXFEmbeddingParameter.type
  override final def embeddingParameter: FOMLToTXFEmbeddingParameter.type = FOMLToTXFEmbeddingParameter

  override final val name: String = "$$fomlModel"
  override final val version: String = "1.2.4"

  override final def generateSpecification(specs: Map[String, String]): TPTP.TFFAnnotated =
    generateTFFSpecification(name, Seq("$modalities", "$quantification", "$constants") , specs)

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[FOMLToTXFEmbeddingParameter.Value]): TPTP.Problem =
    new FirstOrderManySortedToTXFEmbeddingImpl(problem, embeddingOptions).apply()

  override final def apply(formulas: Seq[TPTP.AnnotatedFormula],
                           embeddingOptions: Set[FOMLToTXFEmbeddingParameter.Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  /////////////////////////////////////////////////////////////////////////////////////////////
  /////////////// Embedding implementation BEGIN
  /////////////////////////////////////////////////////////////////////////////////////////////
  private[this] final class FirstOrderManySortedToTXFEmbeddingImpl(problem: TPTP.Problem,
                                                                   embeddingOptions: Set[FOMLToTXFEmbeddingParameter.Value])
    extends ModalEmbeddingLike {

    import FOMLToTXFEmbeddingParameter._

    // Semantics dimensions
    // (1) Rigid or flexible symbols
    private[this] var rigidityMap: Map[String, Rigidity] = Map.empty
    private[this] var reverseSymbolTypeMap: Map[TFF.Type, Set[String]] = Map.empty.withDefaultValue(Set.empty)
    private[this] var rigidityDefaultExists: Boolean = false
    /* Initialize map */
    tptpDefinedPredicateSymbols.foreach { pred => rigidityMap += (pred -> Rigid) }
    tptpDefinedFunctionSymbols.foreach { pred => rigidityMap += (pred -> Rigid) }

    // (2) Quantification semantics
    private[this] var domainMap: Map[TFF.Type, DomainType] = Map.empty
    /* Initialize map: Everything with dollar (or dollar dollar) is interpreted, so it's contant domain. */
    tptpInterpretedTypeNames.foreach { ty => domainMap += (stringToTFFType(ty) -> ConstantDomain) }

    // (3) Modal operator properties, for now as string
    private[this] var modalsMap: Map[TFF.Term, Seq[String]] = Map.empty
    private[this] var modalDefaultExists: Boolean = false
    ////////////////////////////////////////////////////////////////////
    // Embedding options
    private[this] val polymorphic: Boolean = embeddingOptions.contains(POLYMORPHIC) // default monomorphic
    private[this] val localExtension: Boolean = embeddingOptions.contains(LOCALEXTENSION) // default non-local extensions
    private[this] val allowEmptyDomains: Boolean = embeddingOptions.contains(EMPTYDOMAINS) // default non-empty domains
    ////////////////////////////////////////////////////////////////////

    def apply(): TPTP.Problem = {
      val formulas = problem.formulas
      val (spec, sortFormulas, typeFormulas, definitionFormulas, otherFormulas) = splitTFFInputByDifferentKindOfFormulas(formulas)
      val (conjectureFormulas, nonConjectureFormulas) = otherFormulas.partition(_.role.startsWith("conjecture"))

      createState(spec)
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertAnnotatedFormula)
      val convertedNonConjectureFormulas = nonConjectureFormulas.map(convertAnnotatedFormula)
      val convertedConjectureFormulasAsOne = if (conjectureFormulas.nonEmpty) Seq(convertConjectureFormulasIntoOne(conjectureFormulas)) else Seq.empty
      val generatedMetaPreFormulas: Seq[AnnotatedFormula] = generateMetaPreFormulas()
      val generatedMetaPostFormulas: Seq[AnnotatedFormula] = generateMetaPostFormulas()

      val result = sortFormulas ++ generatedMetaPreFormulas ++ convertedTypeFormulas ++
        generatedMetaPostFormulas ++ convertedDefinitionFormulas  ++ convertedNonConjectureFormulas ++ convertedConjectureFormulasAsOne
      val extraComments = generateExtraComments(warnings.toSeq, result.headOption,
        sortFormulas.headOption, generatedMetaPreFormulas.headOption, convertedTypeFormulas.headOption,
        generatedMetaPostFormulas.headOption, convertedDefinitionFormulas.headOption, convertedNonConjectureFormulas.headOption)
      val updatedComments = problem.formulaComments.concat(extraComments)
      TPTP.Problem(problem.includes, result, updatedComments)
    }

    // For warnings that should go inside the output file
    private[this] val warnings: collection.mutable.Buffer[String] = collection.mutable.Buffer.empty

    @inline private[this] val worldTypeName: String = "'$ki_world'"
    @inline private[this] def worldType: TFF.Type = TFF.AtomicType(worldTypeName, Seq.empty)
    @inline private[this] val accessibilityRelationName: String = "'$ki_accessible'"
    @inline private[this] val localWorldName: String = "'$ki_local_world'"
    @inline private[this] def localWorldVariableName: String = "W"
    @inline private[this] def localWorldConstant: TFF.Term = TFF.AtomicTerm(localWorldName, Seq.empty)
    @inline private[this] def localWorldVariable: TFF.Term = TFF.Variable(localWorldVariableName)
    @inline private[this] val indexTypeName: String = "'$ki_index'"
    @unused @inline private[this] def indexType: TFF.Type = TFF.AtomicType(indexTypeName, Seq.empty)
    @inline private[this] val existencePredicateName: String = "'$ki_exists_in_world'"
    /* This only has to work for first-order types, so just pretty instead of encodeType: */
    @inline private[this] def existencePredicateNameForType(ty: TFF.Type): String = s"'${unescapeTPTPName(existencePredicateName)}_${ty.pretty}'"
    private[this] val indexValues: collection.mutable.Set[TFF.Term] = collection.mutable.Set.empty
    @inline private[this] def multimodal(idx: TFF.Term): Unit = {
      indexValues.addOne(idx)
    }
    private[this] val quantifierTypes: collection.mutable.Set[TFF.Type] = collection.mutable.Set.empty
    private[this] def existencePredicate(typ: TFF.Type, worldPlaceholder: TFF.Term, variableName: String): TFF.Formula = {
      typ match {
        case TFF.AtomicType(typName, _) =>
          quantifierTypes.addOne(typ)
          if (polymorphic) TFF.AtomicFormula(existencePredicateName, Seq(TFF.AtomicTerm(typName, Seq.empty), worldPlaceholder, TFF.Variable(variableName)))
          else TFF.AtomicFormula(existencePredicateNameForType(typ), Seq(worldPlaceholder, TFF.Variable(variableName)))
        case _ => throw new EmbeddingException(s"Illegal quantification over non-atomic type '${typ.pretty}'.")
      }
    }

    private[this] def isMultiModal: Boolean = { indexValues.nonEmpty }
    private[this] var isS5 = false // True iff mono-modal and modality is S5
    private[this] var headless = true // True iff embedding is used for model verification only (i.e., modal logic parameters were not given in logic spec)

    private[this] def escapeType(ty: TFF.Type): TFF.Type = {
      ty match {
        case TFF.AtomicType("$ki_world", Seq()) => worldType
        case TFF.MappingType(left, right) =>
          val escapedLeft = left.map(escapeType)
          TFF.MappingType(escapedLeft, escapeType(right))
        case TFF.QuantifiedType(variables, body) =>
          TFF.QuantifiedType(variables, escapeType(body))
        case TFF.TupleType(components) => TFF.TupleType(components.map(escapeType))
        case _ => ty
      }
    }
    private[this] def convertTypeFormula(input: TFFAnnotated): TFFAnnotated = {
      input.formula match {
        case TFF.Typing(atom, typ) =>
          val escapedTyp = escapeType(typ)
          val (argTypes, goalTy) = argumentTypesAndGoalTypeOfTFFType(escapedTyp)
          val convertedType = goalTy match {
            case o@TFF.AtomicType("$o", _) => TFF.MappingType(worldType +: argTypes, o)
            case _ => escapedTyp
          }
          reverseSymbolTypeMap = reverseSymbolTypeMap + (convertedType -> (reverseSymbolTypeMap(convertedType) + atom))
          TFFAnnotated(input.name, input.role, TFF.Typing(atom, convertedType), input.annotations)
        case _ => throw new EmbeddingException(s"Malformed type definition in formula '${input.name}', aborting.")
      }
    }

    private[this] def convertConjectureFormulasIntoOne(input: Seq[TFFAnnotated]): TFFAnnotated = {
      val convertedConjectures = input.map { f =>
        f.formula match {
          case TFF.Logical(formula) => convertAnnotatedFormula0(formula, f.role)
          case _ => throw new EmbeddingException(s"Malformed annotated formula '${f.pretty}'.")
        }
      }
      val formulaAsOne = convertedConjectures.reduce(TFF.BinaryFormula(TFF.&, _, _))
      TFFAnnotated("verify", "conjecture", TFF.Logical(formulaAsOne), None)
    }

    private[this] def convertAnnotatedFormula0(formula: TFF.Formula, role: String): TFF.Formula = {
      import leo.modules.tptputils._
      var globalFormula = false
      var interpretationFormula = false
      val worldPlaceholder = role match {
        case "hypothesis" | "conjecture" => // assumed to be local
          localWorldConstant
        case "interpretation" => // no grounding, just use localWorldConstant as dummy
          interpretationFormula = true; localWorldConstant
        case _ if isSimpleRole(role) => // everything else is assumed to be global
          globalFormula = true; localWorldVariable
        case _ => // role with subroles, check whether a subrole specified $local or $global explicitly
          getSubrole(role).get match {
            case "local" =>
              localWorldConstant
            case "global" =>
              globalFormula = true; localWorldVariable
            case x => throw new EmbeddingException(s"Unknown subrole '$x' in conversion of formula '$name'. ")
          }
      }
      val convertedFormula0: TFF.Formula = if (globalFormula) convertFormula(formula, worldPlaceholder, Set(localWorldVariableName)) else if (interpretationFormula) convertInterpretationFormula(formula) else convertFormula(formula, worldPlaceholder)
      // Ground, if necessary, with "global" quantification
      if (globalFormula) TFF.QuantifiedFormula(TFF.!, Seq((localWorldVariableName, Some(worldType))), convertedFormula0)
      else convertedFormula0
    }

    private[this] def convertAnnotatedFormula(input: TFFAnnotated): TFFAnnotated = {
      import leo.modules.tptputils._
      input.formula match {
        case TFF.Logical(formula) =>
          val convertedFormula = convertAnnotatedFormula0(formula, input.role)
          // Strip local, global etc. role contents from role (as classical ATPs cannot deal with it)
          // And normalize hypothesis to axiom.
          val updatedRole = toSimpleRole(input.role) match {
            case "hypothesis" => "axiom"
            case "interpretation" => "axiom"
            case r => r
          }
          TFFAnnotated(input.name, updatedRole, TFF.Logical(convertedFormula), input.annotations)
        case _ => throw new EmbeddingException(s"Malformed annotated formula '${input.pretty}'.")
      }
    }


    // Interpretation formulas are interpreted specially (like hybrid logic, specifically on worlds).
    private[this] def convertInterpretationFormula(formula: TFF.Formula): TFF.Formula = {
      formula match {
        case TFF.AtomicFormula("$ki_accessible", Seq(w, v)) => TFF.AtomicFormula(accessibilityRelationName, Seq(w, v))
        case TFF.AtomicFormula("$ki_world_is", Seq(world, TFF.FormulaTerm(worldFormula))) =>
          convertFormula(worldFormula, worldPlaceholder = world)
        case TFF.Equality(left, right) => TFF.Equality(convertInterpretationTerm(left),convertInterpretationTerm(right))
        case TFF.Inequality(left, right) => TFF.Inequality(convertInterpretationTerm(left),convertInterpretationTerm(right))

        case TFF.QuantifiedFormula(quantifier, variableList, body) =>
          val escapedVariableList = variableList.map { case (name, maybeTy) =>
            (name, maybeTy.map(escapeType))
          }
          TFF.QuantifiedFormula(quantifier, escapedVariableList, convertInterpretationFormula(body))
        case TFF.UnaryFormula(connective, body) => TFF.UnaryFormula(connective, convertInterpretationFormula(body))
        case TFF.BinaryFormula(connective, left, right) => TFF.BinaryFormula(connective, convertInterpretationFormula(left), convertInterpretationFormula(right))
        case _ => formula
      }
    }
    private[this] def convertInterpretationTerm(term: TFF.Term): TFF.Term = {
      term match {
        case TFF.AtomicTerm("$ki_local_world", Seq()) => localWorldConstant
        case TFF.FormulaTerm(formula) => TFF.FormulaTerm(convertInterpretationFormula(formula))
        case _ => term
      }
    }

    // Non-interpretation formulas are embedded as usual
    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term): TFF.Formula =
      convertFormula(formula, worldPlaceholder, Set.empty)
    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term, boundVars: Set[String]): TFF.Formula = {
      formula match {
        case TFF.AtomicFormula(f, args) => if (f.startsWith("$") || f.startsWith("$$")) formula else TFF.AtomicFormula(f, worldPlaceholder +: args)
        case TFF.UnaryFormula(connective, body) => TFF.UnaryFormula(connective, convertFormula(body, worldPlaceholder, boundVars))
        case TFF.BinaryFormula(connective, left, right) => TFF.BinaryFormula(connective,
                                                                             convertFormula(left, worldPlaceholder, boundVars),
                                                                             convertFormula(right, worldPlaceholder, boundVars))
        case TFF.Equality(left,right) => TFF.Equality(convertTerm(left, worldPlaceholder, boundVars), convertTerm(right, worldPlaceholder, boundVars))
        case TFF.Inequality(left, right) => TFF.Inequality(convertTerm(left, worldPlaceholder, boundVars), convertTerm(right, worldPlaceholder, boundVars))
        case TFF.ConditionalFormula(condition, thn, els) => TFF.ConditionalFormula(convertFormula(condition, worldPlaceholder, boundVars),
                                                                                   convertTerm(thn, worldPlaceholder, boundVars),
                                                                                   convertTerm(els, worldPlaceholder, boundVars))
        case TFF.LetFormula(typing, binding, body) => TFF.LetFormula(typing,
                                                                     binding.map { case (l,r) => (l, convertTerm(r, worldPlaceholder, boundVars))},
                                                                     convertTerm(body, worldPlaceholder, boundVars))
        case TFF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedBody0 = convertFormula(body, worldPlaceholder, boundVars)
          val existenceGuards: Seq[TFF.Formula] = variableList.map { case (varName, maybeType) =>
            maybeType match {
              case Some(ty) => existencePredicate(ty, worldPlaceholder, varName)
              case None => existencePredicate(TFF.AtomicType("$i", Seq.empty), worldPlaceholder, varName)
            }
          }
          val conjunctionOfGuards: TFF.Formula = existenceGuards.reduce(TFF.BinaryFormula(TFF.&, _, _))
          val convertedBody: TFF.Formula = quantifier match {
            case TFF.! => TFF.BinaryFormula(TFF.Impl, conjunctionOfGuards, convertedBody0)
            case TFF.? => TFF.BinaryFormula(TFF.&, conjunctionOfGuards, convertedBody0)
          }
          TFF.QuantifiedFormula(quantifier, variableList, convertedBody)
        case TFF.NonclassicalPolyaryFormula(connective, args) => args match {
          case Seq(body) => connective match {
            case TFF.NonclassicalLongOperator(name, idx, parameters) if synonymsForBox.contains(name) =>
              if (parameters.nonEmpty) throw new EmbeddingException(s"Illegal arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
              else convertBoxModality(body, boundVars, world = worldPlaceholder, index = idx)

            case TFF.NonclassicalLongOperator(name, idx, parameters) if synonymsForDiamond.contains(name) =>
              if (parameters.nonEmpty) throw new EmbeddingException(s"Illegal arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
              else convertDiaModality(body, boundVars, world = worldPlaceholder, index = idx)

            case TFF.NonclassicalBox(index) => convertBoxModality(body, boundVars, world = worldPlaceholder, index)
            case TFF.NonclassicalDiamond(index) => convertDiaModality(body, boundVars, world = worldPlaceholder, index)
            case _ => throw new EmbeddingException(s"Illegal connective '${connective.pretty}' in formula '${formula.pretty}'.")
          }
          case _ => throw new EmbeddingException(s"Illegal number of arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
        }
        case TFF.FormulaVariable(name) => throw new EmbeddingException(s"Quantification over propositions not supported in first-order modal logic embedding but '${formula.pretty}' found. Use higher-order modal logic embedding instead (using parameter '-p FORCE_HIGHERORDER').")
        case TFF.Assignment(_, _) | TFF.MetaIdentity(_, _) => throw new EmbeddingException(s"Unexpected formula '${formula.pretty}' in embedding.")
      }
    }

    private[this] sealed abstract class BoxOrDiamond
    private[this] final object Box extends BoxOrDiamond
    private[this] final object Diamond extends BoxOrDiamond
    private[this] def convertModality(modality: BoxOrDiamond, body: TFF.Formula, boundVars: Set[String], world: TFF.Term, index: Option[TFF.Term]): TFF.Formula = {
      val newWorldVariableName = generateFreshWorldVariable(boundVars)
      val newWorldVariable: TFF.Term = TFF.Variable(newWorldVariableName)
      val convertedBody0 = convertFormula(body, newWorldVariable, boundVars + newWorldVariableName )
      val convertedAccessibilityRelation: TFF.Formula = index match {
        case None =>
          TFF.AtomicFormula(accessibilityRelationName, Seq(world, newWorldVariable))
        case Some(idx) =>
          val escapedIndex = escapeIndex(idx)
          multimodal(escapedIndex)
          TFF.AtomicFormula(accessibilityRelationName, Seq(escapedIndex, world, newWorldVariable))
      }
      modality match {
        case Box =>
          val convertedBody = TFF.BinaryFormula(TFF.Impl, convertedAccessibilityRelation, convertedBody0)
          TFF.QuantifiedFormula(TFF.!, Seq((newWorldVariableName, Some(worldType))), convertedBody)
        case Diamond =>
          val convertedBody = TFF.BinaryFormula(TFF.&, convertedAccessibilityRelation, convertedBody0)
          TFF.QuantifiedFormula(TFF.?, Seq((newWorldVariableName, Some(worldType))), convertedBody)
      }
    }
    @inline private[this] def convertBoxModality(body: TFF.Formula, boundVars: Set[String], world: TFF.Term, index: Option[TFF.Term]): TFF.Formula =
      convertModality(Box, body, boundVars, world, index)
    @inline private[this] def convertDiaModality(body: TFF.Formula, boundVars: Set[String], world: TFF.Term, index: Option[TFF.Term]): TFF.Formula =
      convertModality(Diamond, body, boundVars, world, index)

    private[this] def generateFreshWorldVariable(boundVars: Set[String]): String = generateFreshTPTPVariableName(localWorldVariableName, boundVars)

    private[this] def escapeIndex(idx: TFF.Term): TFF.Term = {
      val escaped = idx match {
        case TFF.AtomicTerm(f, Seq()) => escapeAtomicWord(s"#idx($f)")
        case TFF.NumberTerm(value) => escapeAtomicWord(s"#idx(${value.pretty})")
        case _ => throw new EmbeddingException(s"Only numbers or constants allowed as index value to modal operators, but '${idx.pretty}' was given.")
      }
      TFF.AtomicTerm(escaped, Seq.empty)
    }

    private[this] def convertTerm(term: TFF.Term, worldPlaceholder: TFF.Term, boundVars: Set[String]): TFF.Term = {
      term match {
        /* special cases */
        case TFF.AtomicTerm("$ki_local_world", Seq()) => localWorldConstant
        /* special cases END */
        case TFF.FormulaTerm(formula) => TFF.FormulaTerm(convertFormula(formula, worldPlaceholder, boundVars))
        case _ => term
      }
    }

    /* All the meta formulas that move BEFORE user-type definitions. */
    private def generateMetaPreFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable
      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty

      // Introduce world type and current world
      result.append(worldTypeTPTPDef())
      result.append(localWorldTPTPDef())
      // Introduce type of index values and index typings (if applicable)
      if (isMultiModal) {
        result.append(indexTypeTPTPDef())
        result.append(multiModalAccessbilityRelationTPTPDef())
        indexValues foreach { term =>
          result.append(indexTPTPDef(term))
        }
      } else {
        result.append(accessbilityRelationTPTPDef())
      }
      // Specify properties on accessibility relation if not headless
      if (!headless) {
        if (isMultiModal) {
          indexValues foreach { term =>
            val modalSystem = modalsMap.get(term) match {
              case Some(value) => value
              case None => if (modalDefaultExists) modalsMap.default(term) else throw new EmbeddingException(s"Modal properties for index '${term.pretty}' not defined; and no default properties specified. Aborting.")
            }
            val axiomNames = if (isModalSystemName(modalSystem.head)) modalSystemTable(modalSystem.head) else modalSystem
            axiomNames foreach { ax =>
              val axiom = axiomTable(Some(term))(ax)
              axiom.foreach {
                result.append
              }
            }
          }
        } else {
          val modalSystemOrAxiomNameList = if (modalDefaultExists) modalsMap.default(TFF.AtomicTerm("*dummy*", Seq.empty)) else throw new EmbeddingException(s"Modal operator properties not specified. Aborting.")
          val axiomNames = if (isModalSystemName(modalSystemOrAxiomNameList.head)) {
            val systemName = modalSystemOrAxiomNameList.head
            if (systemName == "$modal_system_S5") {
              isS5 = true
            }
            modalSystemTable(modalSystemOrAxiomNameList.head)
          } else modalSystemOrAxiomNameList
          val modalAxioms = axiomNames.flatMap(axiomTable(None)).toSet
          result.appendAll(modalAxioms)
        }
      }
      result.toSeq
    }

    private def generateMetaPostFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty

      // define exists-in-world-predicate
      if (polymorphic) {
        if (quantifierTypes.nonEmpty) result.append(existsInWorldPredicatePolyTPTPDef())
      } else {
        quantifierTypes.foreach { ty =>
          result.append(existsInWorldPredicateTPTPDef(ty))
        }
      }
      // Specify properties on eiw-predicate if required
      if (!headless) {
        if (isS5) {
          /* Special case: if it's S5 (and mono-modal), every domain is identical. So specify constant domain for every type. */
          quantifierTypes.foreach { ty =>
            result.append(constantExistsInWorldTPTPDef(poly = polymorphic, ty))
          }
        } else {
          quantifierTypes.foreach { ty =>
            domainMap(ty) match { // FIXME: What's up the multi-modal eiw?
              case ConstantDomain => result.append(constantExistsInWorldTPTPDef(poly = polymorphic, ty))
              case CumulativeDomain => result.append(cumulativeExistsInWorldTPTPDef(poly = polymorphic, ty))
              case DecreasingDomain => result.append(decreasingExistsInWorldTPTPDef(poly = polymorphic, ty))
              case VaryingDomain => /* nothing */
            }
          }
        }
        if (!allowEmptyDomains && quantifierTypes.nonEmpty) {
          quantifierTypes.foreach { ty =>
            result.append(existsInWorldNonEmptyTPTPDef(poly = polymorphic, ty))
          }
        }
        // Specify exist-in-world for constants if local extension
        if (localExtension && quantifierTypes.nonEmpty) {
          quantifierTypes.foreach { ty =>
            val symbolsOfThatType = reverseSymbolTypeMap(ty)
            symbolsOfThatType.foreach { sym =>
              result.append(symbolExistsInAllWorldsTPTPDef(poly = polymorphic, ty, sym))
            }
          }
        }
      }

      result.toSeq
    }

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(worldTypeName)}_type"
      annotatedTFF(s"tff(${escapeName(name)}, type, $worldTypeName: $$tType).")
    }

    private[this] def localWorldTPTPDef(): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(localWorldName)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $localWorldName: $worldTypeName).")
    }

    private[this] def accessbilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      val name = unescapeTPTPName(accessibilityRelationName) + "_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $accessibilityRelationName: ($worldTypeName * $worldTypeName) > $$o).")
    }

    private[this] def indexTypeTPTPDef(): TPTP.AnnotatedFormula = {
      val name = unescapeTPTPName(indexTypeName) + "_type"
      annotatedTFF(s"tff(${escapeName(name)}, type, $indexTypeName: $$tType).")
    }

    private[this] def indexTPTPDef(term: TFF.Term): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(term.pretty)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, ${term.pretty}: $indexTypeName).")
    }

    private[this] def multiModalAccessbilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(accessibilityRelationName)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $accessibilityRelationName: ($indexTypeName * $worldTypeName * $worldTypeName) > $$o).")
    }

    private[this] def existsInWorldPredicateTPTPDef(ty: TFF.Type): TPTP.AnnotatedFormula = {
      val eiwPredicateName = existencePredicateNameForType(ty)
      val name = s"${unescapeTPTPName(eiwPredicateName)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $eiwPredicateName: ($worldTypeName * ${ty.pretty}) > $$o).")
    }

    private[this] def existsInWorldPredicatePolyTPTPDef(): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(existencePredicateName)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $existencePredicateName: !>[T:$$tType]: (($worldTypeName * T) > $$o) ).")
    }

    private[this] def existsInWorldNonEmptyTPTPDef(poly: Boolean, ty: TPTP.TFF.Type): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTFF
      val ty0 = ty.pretty
      val name = s"${unescapeTPTPName(existencePredicateName)}_${ty0}_nonempty"
      if (poly) annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName]: ?[X:$ty0]: ( $existencePredicateName($ty0,W,X) )).")
      else annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName]: ?[X:$ty0]: ( ${existencePredicateNameForType(ty)}(W,X) )).")
    }

    private[this] def constantExistsInWorldTPTPDef(poly: Boolean, ty: TFF.Type): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTFF
      val ty0 = ty.pretty
      val name = s"${unescapeTPTPName(existencePredicateName)}_${ty0}_const"
      if (poly) annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, X:$ty0]: ( $existencePredicateName($ty0,W,X) )).")
      else annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, X:$ty0]: ( ${existencePredicateNameForType(ty)}(W,X) )).")
    }

    private[this] def cumulativeExistsInWorldTPTPDef(poly: Boolean, ty: TFF.Type): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTFF
      val ty0 = ty.pretty
      val name = s"${unescapeTPTPName(existencePredicateName)}_${ty0}_cumul"
      if (poly) annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, V:$worldTypeName, X:$ty0]: ( ($existencePredicateName($ty0,W,X) & $accessibilityRelationName(W,V)) => $existencePredicateName($ty0,V,X) )).")
      else annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, V:$worldTypeName, X:$ty0]: ( (${existencePredicateNameForType(ty)}(W,X) & $accessibilityRelationName(W,V)) => ${existencePredicateNameForType(ty)}(V,X) )).")
    }

    private[this] def decreasingExistsInWorldTPTPDef(poly: Boolean, ty: TFF.Type): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTFF
      val ty0 = ty.pretty
      val name = s"${unescapeTPTPName(existencePredicateName)}_${ty0}_decr"
      if (poly) annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, V:$worldTypeName, X:$ty0]: ( ($existencePredicateName($ty0,W,X) & $accessibilityRelationName(V,W)) => $existencePredicateName($ty0,V,X) )).")
      else annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName, V:$worldTypeName, X:$ty0]: ( (${existencePredicateNameForType(ty)}(W,X) & $accessibilityRelationName(V,W)) => ${existencePredicateNameForType(ty)}(V,X) )).")
    }

    private[this] def symbolExistsInAllWorldsTPTPDef(poly: Boolean, ty: TPTP.TFF.Type, symbol: String): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTFF
      val ty0 = ty.pretty
      val name = s"${unescapeTPTPName(symbol)}_exists"
      if (poly) annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName]: ( $existencePredicateName($ty0,W,$symbol) )).")
      else annotatedTFF(s"tff(${escapeName(name)}, axiom, ![W:$worldTypeName]: ( ${existencePredicateNameForType(ty)}(W,$symbol) )).")
    }

    private[this] def axiomTable(index: Option[TFF.Term])(axiom: String): Option[TFFAnnotated] = {
      import modules.input.TPTPParser.annotatedTFF
      def accRel(left: String, right: String): String = index match {
        case Some(idx) => s"$accessibilityRelationName(${idx.pretty}, $left, $right)"
        case None => s"$accessibilityRelationName($left, $right)"
      }
      def augmentName(basename: String): String = index match {
        case Some(idx) => escapeName(s"${unescapeTPTPName(basename)}_${unescapeTPTPName(idx.pretty)}")
        case None => basename
      }
      axiom match {
        case "$modal_axiom_K" => None
        case "$modal_axiom_T" | "$modal_axiom_M" => Some(
          annotatedTFF(
            s"tff(${augmentName("mrel_reflexive")}, axiom, ![W:$worldTypeName]: (${accRel("W","W")}))."
          )
        )
        case "$modal_axiom_B" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_symmetric")}, axiom, ![W:$worldTypeName, V:$worldTypeName]: ((${accRel("W", "V")}) => (${accRel("V", "W")})))."
        ))
        case "$modal_axiom_D" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_serial")}, axiom, ![W:$worldTypeName]: ?[V:$worldTypeName]: (${accRel("W", "V")}))."
        ))
        case "$modal_axiom_4" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_transitive")}, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((${accRel("W", "V")}) & (${accRel("V", "U")})) => (${accRel("W", "U")})))."
        ))
        case "$modal_axiom_5" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_euclidean")}, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((${accRel("W","U")}) & (${accRel("W","V")})) => (${accRel("U","V")})))."
        ))
        case "$modal_axiom_C4" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_dense")}, axiom, ![W:$worldTypeName,U:$worldTypeName]: ((${accRel("W","U")}) => (? [V:$worldTypeName]: ((${accRel("W","V")}) & (${accRel("V","U")})))))."
        ))
        case "$modal_axiom_CD" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_functional")}, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName]: (((${accRel("W","U")}) & (${accRel("W","V")})) => (U = V)))."
        ))
        case "$modal_axiom_S5U" => Some(annotatedTFF(
          s"tff(${augmentName("mrel_universal")}, axiom, ![W:$worldTypeName,V:$worldTypeName]: (${accRel("W","V")}))."
        ))
        case _ => throw new EmbeddingException(s"Unknown modal axiom name '$axiom'.")
      }
    }

    private[this] def createState(spec: TFFAnnotated): Unit = {
      spec.formula match {
        case TFF.Logical(TFF.AtomicFormula(logicname, Seq())) if Seq("$modal", "$alethic_modal", "$deontic_modal", "$epistemic_modal", name) contains logicname =>
          headless = true
        case TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(logicname, Seq()), TFF.Tuple(spec0))) if Seq("$modal", "$alethic_modal", "$deontic_modal", "$epistemic_modal", name) contains logicname =>
          headless = false
          spec0 foreach {
            case TFF.FormulaTerm(TFF.MetaIdentity(TFF.AtomicTerm(propertyName, Seq()), rhs)) =>
              propertyName match {
                case `logicSpecParamNameTermDesignation` =>
                  warnings.append(s"Parameter '$logicSpecParamNameTermDesignation' currently unsupported; this will probably coincide with global terms.")
                case `logicSpecParamNameRigidity` =>
                  val (default, map) = parseTFFSpecRHS(rhs)
                  if (default.isDefined) {
                    rigidityDefaultExists = true
                  }
                  default match {
                    case Some("$rigid") => rigidityMap = rigidityMap.withDefaultValue(Rigid)
                    case Some("$flexible") => rigidityMap = rigidityMap.withDefaultValue(Flexible)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, rigidity) =>
                    rigidity match {
                      case "$rigid" => rigidityMap += (name -> Rigid)
                      case "$flexible" => rigidityMap += (name -> Flexible)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$rigidity'")
                    }
                  }
                case `logicSpecParamNameQuantification` =>
                  val (default, map) = parseTFFSpecRHS(rhs)
                  default match {
                    case Some("$constant") => domainMap = domainMap.withDefaultValue(ConstantDomain)
                    case Some("$varying") => domainMap = domainMap.withDefaultValue(VaryingDomain)
                    case Some("$cumulative") => domainMap = domainMap.withDefaultValue(CumulativeDomain)
                    case Some("$decreasing") => domainMap = domainMap.withDefaultValue(DecreasingDomain)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, quantification) =>
                    quantification match {
                      case "$constant" => domainMap += (stringToTFFType(name) -> ConstantDomain)
                      case "$varying" => domainMap += (stringToTFFType(name) -> VaryingDomain)
                      case "$cumulative" => domainMap += (stringToTFFType(name) -> CumulativeDomain)
                      case "$decreasing" => domainMap += (stringToTFFType(name) -> DecreasingDomain)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$quantification'")
                    }
                  }
                case `logicSpecParamNameModalities` => val (default, map) = parseTFFListSpecRHS(rhs)
                  if (default.nonEmpty) {
                    modalDefaultExists = true
                    if (default.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec))) {
                      modalsMap = modalsMap.withDefaultValue(default)
                    } else throw new EmbeddingException(s"Unknown modality specification: ${default.mkString("[", ",", "]")}")
                  }
                  map foreach { case (lhs, modalspec) =>
                    val index0 = lhs match {
                      case TFF.FormulaTerm(TFF.NonclassicalPolyaryFormula(TFF.NonclassicalBox(Some(index)), Seq())) => index
                      case TFF.FormulaTerm(TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(cname, Some(index), Seq()), Seq()))
                        if synonymsForBox.contains(cname) => index
                      case _ => throw new EmbeddingException(s"Modality specification did not start with '[#idx] == ...' or '{#box(#idx)} == ...'.")
                    }
                    val index = escapeIndex(index0)
                    if (modalspec.nonEmpty) {
                      if (modalspec.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec))) {
                        modalsMap = modalsMap + (index -> modalspec)
                      } else throw new EmbeddingException(s"Unknown modality specification: ${modalspec.mkString("[", ",", "]")}")
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

  /////////////////////////////////////////////////////////////////////////////////////////////
  /////////////// Embedding implementation END
  /////////////////////////////////////////////////////////////////////////////////////////////

}
