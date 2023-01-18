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

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =  { ??? }

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

      createState(spec)
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertAnnotatedFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      val result = sortFormulas ++ generatedMetaFormulas ++ convertedTypeFormulas ++ convertedDefinitionFormulas  ++ convertedOtherFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }

    @inline private[this] val worldTypeName: String = "mworld"
    @inline private[this] def worldType: TFF.Type = TFF.AtomicType(worldTypeName, Seq.empty)
    @inline private[this] val accessibilityRelationName: String = "mrel"
    @inline private[this] val localWorldName: String = "cw"
    @inline private[this] def localWorldVariableName: String = localWorldName.toUpperCase
    @inline private[this] def localWorldConstant: TFF.Term = TFF.AtomicTerm(localWorldName, Seq.empty)
    @inline private[this] def localWorldVariable: TFF.Term = TFF.Variable(localWorldVariableName)
    @inline private[this] val indexTypeName: String = "mindex"
    @inline private[this] def indexType: TFF.Type = TFF.AtomicType(indexTypeName, Seq.empty)

    private[this] val indexValues: collection.mutable.Set[TFF.Term] = collection.mutable.Set.empty
    private def multimodal(idx: TFF.Term): Unit = {
      indexValues.addOne(idx)
    }
    private def isMultiModal: Boolean = { indexValues.nonEmpty }

    private[this] def argumentTypesAndGoalTypeOfType(ty: TFF.Type): (Seq[TFF.Type], TFF.Type) = ty match {
      case TFF.AtomicType(_, _) => (Seq.empty, ty)
      case TFF.MappingType(left, right) => (left, right)
      case _ => throw new EmbeddingException(s"Unexpected error in argumentAndGoalTypeOfType(ty = ${ty.pretty}).")
    }
    private[this] def convertTypeFormula(input: TFFAnnotated): TFFAnnotated = {
      input.formula match {
        case TFF.Typing(atom, typ) =>
          val (argTypes, goalTy) = argumentTypesAndGoalTypeOfType(typ)
          val convertedType = goalTy match {
            case o@TFF.AtomicType("$o", _) => TFF.MappingType(worldType +: argTypes, o)
            case _ => typ
          }
          TFFAnnotated(input.name, input.role, TFF.Typing(atom, convertedType), input.annotations)
        case _ => throw new EmbeddingException(s"Malformed type definition in formula '${input.name}', aborting.")
      }
    }

    private[this] def convertAnnotatedFormula(input: TFFAnnotated): TFFAnnotated = {
      import leo.modules.tptputils._
      input.formula match {
        case TFF.Logical(formula) =>
          var globalFormula = false
          val worldPlaceholder = input.role match {
            case "hypothesis" | "conjecture" => // assumed to be local
              localWorldConstant
            case _ if isSimpleRole(input.role) => // everything else is assumed to be global
              globalFormula = true; localWorldVariable
            case _ => // role with subroles, check whether a subrole specified $local or $global explicitly
              getSubrole(input.role).get match {
                case "local" =>
                  localWorldConstant
                case "global" =>
                  globalFormula = true; localWorldVariable
                case x => throw new EmbeddingException(s"Unknown subrole '$x' in conversion of formula '$name'. ")
              }
          }
          // Strip $local, $global etc. role contents from role (as classical ATPs cannot deal with it)
          // And normalize hypothesis to axiom.
          val updatedRole = toSimpleRole(input.role) match {
            case "hypothesis" => "axiom"
            case r => r
          }
          val convertedFormula0: TFF.Formula = if (globalFormula) convertFormula(formula, worldPlaceholder, Set(localWorldName)) else convertFormula(formula, worldPlaceholder)
          // Ground, if necessary, with "global" quantification
          val convertedFormula: TFF.Formula = if (globalFormula) TFF.QuantifiedFormula(TFF.!, Seq((localWorldVariableName, Some(worldType))), convertedFormula0)
                                 else convertedFormula0
          TFFAnnotated(input.name, updatedRole, TFF.Logical(convertedFormula), input.annotations)
        case _ => throw new EmbeddingException(s"Malformed annotated formula '${input.pretty}'.")
      }
    }

    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term): TFF.Formula =
      convertFormula(formula, worldPlaceholder, Set.empty)
    private[this] def convertFormula(formula: TFF.Formula, worldPlaceholder: TFF.Term, boundVars: Set[String]): TFF.Formula = {
      formula match {
        case TFF.AtomicFormula(f, args) => TFF.AtomicFormula(f, worldPlaceholder +: args)
        case TFF.UnaryFormula(connective, body) => TFF.UnaryFormula(connective, convertFormula(body, worldPlaceholder, boundVars))
        case TFF.BinaryFormula(connective, left, right) => TFF.BinaryFormula(connective,
                                                                             convertFormula(left, worldPlaceholder, boundVars),
                                                                             convertFormula(right, worldPlaceholder, boundVars))
        case TFF.Equality(_, _) | TFF.Inequality(_, _) => formula
        case TFF.ConditionalFormula(condition, thn, els) => TFF.ConditionalFormula(convertFormula(condition, worldPlaceholder, boundVars),
                                                                                   convertTerm(thn, worldPlaceholder, boundVars),
                                                                                   convertTerm(els, worldPlaceholder, boundVars))
        case TFF.LetFormula(typing, binding, body) => TFF.LetFormula(typing,
                                                                     binding.map { case (l,r) => (l, convertTerm(r, worldPlaceholder, boundVars))},
                                                                     convertTerm(body, worldPlaceholder, boundVars))
        // TODO: Domain semantics?
        case TFF.QuantifiedFormula(quantifier, variableList, body) => TFF.QuantifiedFormula(quantifier, variableList,
                                                                              convertFormula(body, worldPlaceholder, boundVars))
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
        candidateName = candidateName ++ "W"
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
        case TFF.FormulaTerm(formula) => TFF.FormulaTerm(convertFormula(formula, worldPlaceholder, boundVars))
        case _ => term
      }
    }

    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty
      // Introduce world type
      result.append(worldTypeTPTPDef())
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

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTFF(s"tff(${worldTypeName}_type, type, $worldTypeName: $$tType).")
    }

    private[this] def accessbilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTFF(s"tff(${accessibilityRelationName}_decl, type, $accessibilityRelationName: ($worldTypeName * $worldTypeName) > $$o).")
    }

    private[this] def indexTypeTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTFF(s"tff(${indexTypeName}_type, type, $indexTypeName: $$tType).")
    }

    private[this] def indexTPTPDef(term: TFF.Term): TPTP.AnnotatedFormula = {
      val name = s"${unescapeTPTPName(term.pretty)}_decl"
      annotatedTFF(s"tff($name, type, ${term.pretty}: $indexTypeName).")
    }

    private[this] def multiModalAccessbilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTFF(s"tff(${accessibilityRelationName}_decl, type, $accessibilityRelationName: ($indexTypeName * $worldTypeName * $worldTypeName) > $$o).")
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
