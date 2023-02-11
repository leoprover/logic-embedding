package leo
package modules
package embeddings

import datastructures.TPTP
import TPTP.{AnnotatedFormula, TFF, TFFAnnotated}
import leo.modules.input.TPTPParser.annotatedTFF

object FirstOrderManySortedToTXFEmbedding extends Embedding {

  object FOMLToTXFEmbeddingParameter extends Enumeration { }
  override type OptionType = FOMLToTXFEmbeddingParameter.type

  override final def embeddingParameter: FOMLToTXFEmbeddingParameter.type = FOMLToTXFEmbeddingParameter

  override final val name: String = "$$fomlModel"
  override final val version: String = "1.0"

  override final def generateSpecification(specs: Map[String, String]): TPTP.TFFAnnotated =
    TFFAnnotated("spec", "logic", TFF.Logical(TFF.AtomicFormula(`name`, Seq.empty)), None)

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[FOMLToTXFEmbeddingParameter.Value]): TPTP.Problem =
    new FirstOrderManySortedToTXFEmbeddingImpl(problem).apply()

  override final def apply(formulas: Seq[TPTP.AnnotatedFormula],
                           embeddingOptions: Set[FOMLToTXFEmbeddingParameter.Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  /////////////////////////////////////////////////////////////////////////////////////////////
  /////////////// Embedding implementation BEGIN
  /////////////////////////////////////////////////////////////////////////////////////////////
  private[this] final class FirstOrderManySortedToTXFEmbeddingImpl(problem: TPTP.Problem) {
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
      TPTP.Problem(problem.includes, result, Map.empty)
    }

    @inline private[this] val worldTypeName: String = "'$ki_world'"
    @inline private[this] def worldType: TFF.Type = TFF.AtomicType(worldTypeName, Seq.empty)
    @inline private[this] val accessibilityRelationName: String = "'$ki_accessible'"
    @inline private[this] val localWorldName: String = "'$ki_local_world'"
    @inline private[this] def localWorldVariableName: String = "LOCALWORLD"
    @inline private[this] def localWorldConstant: TFF.Term = TFF.AtomicTerm(localWorldName, Seq.empty)
    @inline private[this] def localWorldVariable: TFF.Term = TFF.Variable(localWorldVariableName)
    @inline private[this] val indexTypeName: String = "'$ki_index'"
    @inline private[this] def indexType: TFF.Type = TFF.AtomicType(indexTypeName, Seq.empty)
    @inline private[this] val existencePredicateName: String = "'$ki_exists_in_world'"
    @inline private[this] def existencePredicateNameForType(ty: String): String = s"'${unescapeTPTPName(existencePredicateName)}_$ty'"
    private[this] val indexValues: collection.mutable.Set[TFF.Term] = collection.mutable.Set.empty
    private def multimodal(idx: TFF.Term): Unit = {
      indexValues.addOne(idx)
    }
    /* It's only base type, as we are first-order: So use strings. */
    private[this] val quantifierTypes: collection.mutable.Set[String] = collection.mutable.Set.empty
    private def existencePredicate(typ: TFF.Type, worldPlaceholder: TFF.Term, variableName: String): TFF.Formula = {
      val typName = typ match {
        case TFF.AtomicType(name, _) => quantifierTypes.addOne(name); name
        case _ => throw new EmbeddingException(s"Illegal quantification over non-atomic type '${typ.pretty}'.")
      }
      TFF.AtomicFormula(existencePredicateNameForType(typName), Seq(worldPlaceholder, TFF.Variable(variableName)))
    }

    private def isMultiModal: Boolean = { indexValues.nonEmpty }

    private[this] def argumentTypesAndGoalTypeOfType(ty: TFF.Type): (Seq[TFF.Type], TFF.Type) = ty match {
      case TFF.AtomicType(_, _) => (Seq.empty, ty)
      case TFF.MappingType(left, right) => (left, right)
      case _ => throw new EmbeddingException(s"Unexpected error in argumentAndGoalTypeOfType(ty = ${ty.pretty}).")
    }
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
          val (argTypes, goalTy) = argumentTypesAndGoalTypeOfType(escapedTyp)
          val convertedType = goalTy match {
            case o@TFF.AtomicType("$o", _) => TFF.MappingType(worldType +: argTypes, o)
            case _ => escapedTyp
          }
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

    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term): TFF.Formula =
      convertFormula(formula, worldPlaceholder, Set.empty)
    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term, boundVars: Set[String]): TFF.Formula = {
      formula match {
        /* special cases */
//        case TFF.AtomicFormula("$accessible_ki_world", Seq(w,v)) => TFF.AtomicFormula(accessibilityRelationName, Seq(w, v))
//        case TFF.AtomicFormula("$in_ki_world", Seq(world, TFF.FormulaTerm(worldFormula))) =>
//          convertFormula(worldFormula, worldPlaceholder =  world, boundVars)
        /* special cases END */
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
            case TFF.NonclassicalLongOperator(name, parameters) if Seq("$box", "$necessary").contains(name) =>
              parameters match {
                case Seq() => convertBoxModality(body, boundVars, world = worldPlaceholder, index = None)
                case Seq(Left(idx)) => convertBoxModality(body, boundVars, world = worldPlaceholder, index = Some(idx))
                case _ => throw new EmbeddingException(s"Illegal arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
              }
            case TFF.NonclassicalLongOperator(name, parameters) if Seq("$dia", "$possible").contains(name) =>
              parameters match {
                case Seq() => convertDiaModality(body, boundVars, world = worldPlaceholder, index = None)
                case Seq(Left(idx)) => convertDiaModality(body, boundVars, world = worldPlaceholder, index = Some(idx))
                case _ => throw new EmbeddingException(s"Illegal arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
              }
            case TFF.NonclassicalBox(index) => convertBoxModality(body, boundVars, world = worldPlaceholder, index)
            case TFF.NonclassicalDiamond(index) => convertDiaModality(body, boundVars, world = worldPlaceholder, index)
            case _ => throw new EmbeddingException(s"Illegal connective '${connective.pretty}' in formula '${formula.pretty}'.")
          }
          case _ => throw new EmbeddingException(s"Illegal number of arguments to connective '${connective.pretty}' in formula '${formula.pretty}'.")
        }
        case TFF.Assignment(_, _) | TFF.MetaIdentity(_, _) | TFF.FormulaVariable(_) => throw new EmbeddingException(s"Unexpected formula '${formula.pretty}' in embedding.")
      }
    }

    private[this] def convertBoxModality(body: TFF.Formula, boundVars: Set[String], world: TFF.Term, index: Option[TFF.Term]): TFF.Formula = {
      val newWorldVariableName = generateFreshWorldVariable(boundVars)
      val newWorldVariable: TFF.Term = TFF.Variable(newWorldVariableName)
      val convertedBody0 = convertFormula(body, newWorldVariable)
      val convertedAccessibilityRelation: TFF.Formula = index match {
        case None =>
          TFF.AtomicFormula(accessibilityRelationName, Seq(world, newWorldVariable))
        case Some(idx) =>
          val escapedIndex = escapeIndex(idx)
          multimodal(escapedIndex)
          TFF.AtomicFormula(accessibilityRelationName, Seq(escapedIndex, world, newWorldVariable))
      }
      val convertedBody = TFF.BinaryFormula(TFF.Impl, convertedAccessibilityRelation, convertedBody0)
      TFF.QuantifiedFormula(TFF.!, Seq((newWorldVariableName, Some(worldType))), convertedBody)
    }

    private[this] def convertDiaModality(body: TFF.Formula, boundVars: Set[String], world: TFF.Term, index: Option[TFF.Term]): TFF.Formula = {
      val newWorldVariableName = generateFreshWorldVariable(boundVars)
      val newWorldVariable: TFF.Term = TFF.Variable(newWorldVariableName)
      val convertedBody0 = convertFormula(body, newWorldVariable)
      val convertedAccessibilityRelation: TFF.Formula = index match {
        case None =>
          TFF.AtomicFormula(accessibilityRelationName, Seq(world, newWorldVariable))
        case Some(idx) =>
          val escapedIndex = escapeIndex(idx)
          multimodal(escapedIndex)
          TFF.AtomicFormula(accessibilityRelationName, Seq(escapedIndex, world, newWorldVariable))
      }
      val convertedBody = TFF.BinaryFormula(TFF.&, convertedAccessibilityRelation, convertedBody0)
      TFF.QuantifiedFormula(TFF.?, Seq((newWorldVariableName, Some(worldType))), convertedBody)
    }

    private[this] def generateFreshWorldVariable(boundVars: Set[String]): String = {
      var candidateName: String = localWorldVariableName
      while (boundVars.contains(candidateName)) {
        candidateName = candidateName ++ "0"
      }
      candidateName
    }
    private[this] def escapeIndex(idx: TFF.Term): TFF.Term = {
      val escaped = idx match {
        case TFF.AtomicTerm(f, Seq()) => escapeAtomicWord(s"index($f)")
        case TFF.NumberTerm(value) => escapeAtomicWord(s"index(${value.pretty})")
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
        result.append(multiModalAccessbilityRelationTPTPDef())
        result.append(indexTypeTPTPDef())
        indexValues foreach { term =>
          result.append(indexTPTPDef(term))
        }
      } else {
        result.append(accessbilityRelationTPTPDef())
      }

      result.toSeq
    }

    private def generateMetaPostFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty

      quantifierTypes.foreach { ty =>
        result.append(existsInWorldPredicateTPTPDef(ty))
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

    private[this] def existsInWorldPredicateTPTPDef(ty: String): TPTP.AnnotatedFormula = {
      val eiwPredicateName = existencePredicateNameForType(ty)
      val name = s"${unescapeTPTPName(eiwPredicateName)}_decl"
      annotatedTFF(s"tff(${escapeName(name)}, type, $eiwPredicateName: ($worldTypeName * $ty) > $$o).")
    }

    private[this] def createState(spec: TFFAnnotated): Unit = {
      spec.formula match {
        case TFF.Logical(TFF.AtomicFormula(`name`, Seq())) =>
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////
  /////////////// Embedding implementation END
  /////////////////////////////////////////////////////////////////////////////////////////////

}
