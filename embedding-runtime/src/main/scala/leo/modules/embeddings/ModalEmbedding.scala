package leo
package modules
package embeddings

import datastructures.TPTP
import TPTP.{AnnotatedFormula, THF, THFAnnotated}

import scala.annotation.unused

object ModalEmbedding extends Embedding with ModalEmbeddingLike {
  object ModalEmbeddingOption extends Enumeration {
    // Hidden on purpose, to allow distinction between the object itself and its values.
    //    type ModalEmbeddingOption = Value
    @unused
    final val MONOMORPHIC, POLYMORPHIC,
    MODALITIES_SEMANTICAL, MODALITIES_SYNTACTICAL,
    DOMAINS_SEMANTICAL, DOMAINS_SYNTACTICAL, FORCE_HIGHERORDER, LOCALEXTENSION, EMPTYDOMAINS = Value
  }

  override type OptionType = ModalEmbeddingOption.type
  override final def embeddingParameter: ModalEmbeddingOption.type = ModalEmbeddingOption

  override final def name: String = "$modal"
  override final def version: String = "2.1.3"

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =
    generateTHFSpecification(name, logicSpecParamNames, specs)

  override final def apply(problem: TPTP.Problem,
                  embeddingOptions: Set[ModalEmbeddingOption.Value]): TPTP.Problem = {
    // If the FORCE_HIGHERORDER parameter is set, the embedding will be to THF regardless whether it's first-order (TFF)
    // or not. If unset, the modal-to-TFF embedding will be used if the logic spec is in TFF, to THF otherwise.
    if (embeddingOptions.contains(ModalEmbeddingOption.FORCE_HIGHERORDER)) new ModalEmbeddingImpl(problem, embeddingOptions).apply()
    else {
      import FirstOrderManySortedToTXFEmbedding.FOMLToTXFEmbeddingParameter
      val maybeSpec = getLogicSpecFromProblem(problem.formulas)
      maybeSpec match {
        case Some(spec) if spec.formulaType == TPTP.AnnotatedFormula.FormulaType.TFF =>
          // Fallback to HOL embedding if problem
          // contains extended specification entries (interaction axioms, meta-axioms, etc....)
          if (testSpecForExtendedEntries(spec)) new ModalEmbeddingImpl(problem, embeddingOptions).apply()
          else {
            System.err.println(s"%%% First-order input detected, trying modal-logic-to-TFX embedding (redirected from embedding '$$$name' to embedding '${FirstOrderManySortedToTXFEmbedding.name}' version ${FirstOrderManySortedToTXFEmbedding.version}) ... Use flag -p FORCE_HIGHERORDER if you want to have THF output instead.")
            /* create new parameter set */
            var parameters: Set[FirstOrderManySortedToTXFEmbedding.FOMLToTXFEmbeddingParameter.Value] = Set.empty
            if (embeddingOptions.contains(ModalEmbeddingOption.POLYMORPHIC)) parameters = parameters + FOMLToTXFEmbeddingParameter.POLYMORPHIC
            if (embeddingOptions.contains(ModalEmbeddingOption.EMPTYDOMAINS)) parameters = parameters + FOMLToTXFEmbeddingParameter.EMPTYDOMAINS
//            if (embeddingOptions.contains(ModalEmbeddingOption.LOCALEXTENSION)) parameters = parameters + FOMLToTXFEmbeddingParameter.LOCALEXTENSION
            try {
              FirstOrderManySortedToTXFEmbedding.apply0(problem, parameters)
            } catch {
              case e:FirstOrderManySortedToTXFEmbedding.UnsupportedFragmentException =>
                System.err.println("%%% Info: Modal-logic-to-TFX embedding failed (due to unsupported language features). Falling back to higher-order embedding ...")
              new ModalEmbeddingImpl(problem, embeddingOptions).apply()
            }

          }
        case _ => new ModalEmbeddingImpl(problem, embeddingOptions).apply()
      }
    }
  }

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
    import scala.collection.mutable
    ///////////////////////////////////////////////////////////////////

    // Semantics dimensions
    // (1) Rigid or flexible symbols
    private[this] var rigidityMap: Map[String, Rigidity] = Map.empty
    private[this] var reverseSymbolTypeMap: Map[THF.Type, Set[String]] = Map.empty.withDefaultValue(Set.empty)
    private[this] var rigidityDefaultExists: Boolean = false
    /* Initialize map */
    tptpDefinedPredicateSymbols.foreach { pred => rigidityMap += (pred -> Rigid) }
    tptpDefinedFunctionSymbols.foreach { pred => rigidityMap += (pred -> Rigid) }

    // (2) Quantification semantics
    private[this] var domainMap: Map[String, DomainType] = Map.empty
    /* Initialize map: Everything with dollar (or dollar dollar) is interpreted, so it's contant domain. */
    domainMap += ("$o" -> ConstantDomain)
    domainMap += ("$int" -> ConstantDomain)
    domainMap += ("$rat" -> ConstantDomain)
    domainMap += ("$real" -> ConstantDomain) // TODO: Rework in ... "if starts with dollar, then constant domain"

    // (3) Modal operator characteristics
    private[this] var modalsMapPredefined: Map[THF.Formula, Seq[String]] = Map.empty
    private[this] var modalsMapFormulas: Map[THF.Formula,Seq[THF.Formula]] = Map.empty
    private[this] var modalsMetaAxioms: Seq[THF.Formula] = Seq.empty
    private[this] var modalDefaultExists: Boolean = false
    ////////////////////////////////////////////////////////////////////
    // Embedding options
    private[this] val polymorphic: Boolean = embeddingOptions.contains(POLYMORPHIC) // default monomorphic
    private[this] val localExtension: Boolean = embeddingOptions.contains(LOCALEXTENSION) // default non-local extensions
    private[this] val allowEmptyDomains: Boolean = embeddingOptions.contains(EMPTYDOMAINS) // default non-empty domains

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

      val (spec,sortFormulas,typeFormulas,definitionFormulas,otherFormulas) = splitTHFInputByDifferentKindOfFormulas(formulas)
      createState(spec)
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedMetaPreFormulas: Seq[AnnotatedFormula] = generateMetaPreFormulas()
      val generatedMetaPostFormulas: Seq[AnnotatedFormula] = generateMetaPostFormulas()

      // new user sorts first (new types), then our types, then user symbol declarations, then remaining meta forulas, then all other formulas
      val result = sortFormulas ++ generatedMetaPreFormulas ++
        convertedTypeFormulas ++ generatedMetaPostFormulas ++
        convertedDefinitionFormulas ++ convertedOtherFormulas
      val extraComments = generateExtraComments(warnings.toSeq, result.headOption,
        sortFormulas.headOption, generatedMetaPreFormulas.headOption, convertedTypeFormulas.headOption,
        generatedMetaPostFormulas.headOption, convertedDefinitionFormulas.headOption, convertedOtherFormulas.headOption)
      val updatedComments = problem.formulaComments.concat(extraComments)

      TPTP.Problem(problem.includes, result, updatedComments)
    }

    private[this] def convertDefinitionFormula(formula: THFAnnotated): AnnotatedFormula = {
      formula match {
        case THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), body)), annotations) =>
          THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), convertFormula(body))), annotations)
        case _ => convertAnnotatedFormula(formula)
      }
    }

    private[this] def convertAnnotatedFormula(formula: THFAnnotated): AnnotatedFormula = {
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

    @inline private[this] def mglobal: THF.Formula = str2Fun("mglobal")
    @inline private[this] def mlocal: THF.Formula = str2Fun("mlocal")

    @inline private def convertFormula(formula: THF.Formula): THF.Formula = convertFormula(formula, Map.empty)
    private def convertFormula(formula: THF.Formula, boundVars: Map[String, THF.Type]): THF.Formula = {
      import TPTP.THF.App

      formula match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = THF.FunctionTerm(f, args.map(convertFormula(_, boundVars)))
          val rigidity = rigidityMap.get(f) match {
            case Some(value) => value
            case None => if (rigidityDefaultExists) rigidityMap.default(f) else throw new EmbeddingException(s"Rigidity of symbol '$f' not defined and no default rigidity specified. Aborting.")
          }
          rigidity match {
            case Rigid => worldAbstraction (convertedArgs, boundVars)
            case Flexible => convertedArgs
          }

        case THF.Variable(_) =>
          worldAbstraction(formula, boundVars) //make type correct by abstraction
//          boundVars.get(name) match {
//            case Some(ty) =>
//              val goal = goalType(ty)
//              goal match { // Special treatment for formulas/predicates: flexible
//                case THF.FunctionTerm("$o", Seq()) => formula
//                case _ => worldAbstraction(formula, boundVars) //make type correct by abstraction
//              }
//            case None => worldAbstraction(formula, boundVars) //loose bound variable, just do anything; the formula is not well-formed anyway.
//          }

        // Special case: Modal operators (they are not constants from the signature)
        case THF.NonclassicalPolyaryFormula(connective, args) =>
          if (args.size == 1) {
            val body = args.head
            val convertedBody = convertFormula(body, boundVars)
            val convertedConnective: THF.Formula = connective match {
              case THF.NonclassicalBox(index) => index match {
                case Some(index0) => mboxIndexed(index0)
                case None => str2Fun("mbox")
              }
              case THF.NonclassicalDiamond(index) => index match {
                case Some(index0) => mdiaIndexed(index0)
                case None => str2Fun("mdia")
              }
              case THF.NonclassicalLongOperator(name, index, parameters) =>
                if (parameters.nonEmpty) throw new EmbeddingException(s"Only up to one index is allowed in box operator, but parameters '${parameters.toString()}' was given.")
                name match {
                  case x if synonymsForBox.contains(x) => index match {
                      case Some(index0) => mboxIndexed(index0)
                      case None => str2Fun("mbox")
                    }
                  case x if synonymsForDiamond.contains(x) => index match {
                    case Some(index0) => mdiaIndexed(index0)
                    case None => str2Fun("mdia")
                  }
                  case "$forbidden" => index match {
                    case Some(index0) =>
                      val box = mboxIndexed(index0)
                      modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                    case None =>
                      val box = str2Fun("mbox")
                      modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                  }
                  case _ => throw new EmbeddingException(s"Unknown connective name '$name'.")
                }
              case _ => throw new EmbeddingException(s"Unsupported non-classical operator: '${connective.pretty}'")
            }
            THF.BinaryFormula(THF.App, convertedConnective, convertedBody)
          } else {
            throw new EmbeddingException(s"Only unary operators supported in modal embedding, but '${formula.pretty}' was given.")
          }
          // Special case END

        case THF.BinaryFormula(connective, left, right) =>
          val convertedLeft: TPTP.THF.Formula = convertFormula(left, boundVars)
          val convertedRight: TPTP.THF.Formula = convertFormula(right, boundVars)
          val safeName = generateSafeName(boundVars) // a name that is not free in the formula
          val appliedLeft = THF.BinaryFormula(THF.App, convertedLeft, THF.Variable(safeName))
          val appliedRight = THF.BinaryFormula(THF.App, convertedRight, THF.Variable(safeName))
          worldAbstraction(THF.BinaryFormula(connective, appliedLeft, appliedRight), safeName)

        case THF.UnaryFormula(connective, body) =>
          /* In theory, this could be rewritten to an application of body to a constant.
             But this results in a ugly formula, because TPTP has a dedicated syntax for unary formulas.
             So we replace the result of doing this with an identical expression that uses a nicer syntax */
          val convertedBody: TPTP.THF.Formula = convertFormula(body, boundVars)
          val safeName = generateSafeName(boundVars) // a name that is not free in the formula
          val appliedBody = THF.BinaryFormula(THF.App, convertedBody, THF.Variable(safeName))
          worldAbstraction(THF.UnaryFormula(connective, appliedBody), safeName)

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          /* in theory, this could be rewritten to a lambda applied to a constant.
             But this results in a ugly formula, because TPTP has a dedicated syntax for quantifications.
             So we replace the result of doing this with an identical expression that uses a nicer syntax */
          val updatedBoundVars = boundVars.concat(variableList)
          val convertedBody = convertFormula(body, updatedBoundVars)
          val safeName = generateSafeName(updatedBoundVars) // a name that is not free in the formula
          val appliedBody: THF.Formula = THF.BinaryFormula(App, convertedBody, THF.Variable(safeName))
          // Step through variables one-by-one to allow introducing exists-in-world-predicates
          val result = variableList.foldRight(appliedBody)(mkSingleQuantified(quantifier, safeName))
          worldAbstraction(result, safeName)

        case THF.ConnectiveTerm(_) =>
          worldAbstraction(formula, boundVars) // connectives are rigid: so do a world abstraction

        // TPTP special cases BEGIN
        case THF.Tuple(elements) =>
          val convertedElements: Seq[TPTP.THF.Formula] = elements.map(convertFormula(_, boundVars))
          THF.Tuple(convertedElements)

        case THF.ConditionalTerm(condition, thn, els) =>
          val convertedCondition: TPTP.THF.Formula = convertFormula(condition, boundVars)
          val convertedThn: TPTP.THF.Formula = convertFormula(thn, boundVars)
          val convertedEls: TPTP.THF.Formula = convertFormula(els, boundVars)
          val safeName = generateSafeName(boundVars) // a name that is not free in the formula
          val appliedCond = THF.BinaryFormula(THF.App, convertedCondition, THF.Variable(safeName))
          val appliedThn = THF.BinaryFormula(THF.App, convertedThn, THF.Variable(safeName))
          val appliedEls = THF.BinaryFormula(THF.App, convertedEls, THF.Variable(safeName))
          worldAbstraction(THF.ConditionalTerm(appliedCond, appliedThn, appliedEls), safeName)

        case THF.LetTerm(_, _, _) => // Treat new symbols like bound variables // TODO
          throw new EmbeddingException("TPTP let statements currently not supported. Aborting.")
        // TPTP special cases END

        /* Remaining cases are:
        *  - THF.DefinedTH1ConstantTerm(_)
        *  - THF.DistinctObject(_)
        *  - THF.NumberTerm(_).
        * They are all the same (rigid constants). */
        case _ => worldAbstraction(formula, boundVars)
      }
    }

    private def convertSyntacticPreFormula(formula: THF.Formula, boundVars: Map[String, THF.Type],unboundVars0: Seq[String], specIndex: Option[TPTP.THF.FunctionTerm]): (THF.Formula,Seq[String]) = {
      // convertSyntacticPreFormula returns a Sequence of the unbound variables in addition to the converted formula
      // this is necessary in order to quantify over unbound variables as meta-logic formulas

      import TPTP.THF.App
      val metaFormulaType = THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), THF.FunctionTerm(s"$$o", Seq.empty))

      formula match {
        case THF.FunctionTerm(f, args) =>
          // generate a sequence containing the unbound variables that occur in the arguments
          val unboundVars = args.flatMap(convertSyntacticPreFormula(_, boundVars, unboundVars0, specIndex)._2)
          // convert the arguments
          val convertedArgs = THF.FunctionTerm(f, args.map(convertSyntacticPreFormula(_, boundVars, unboundVars, specIndex)._1))
          val rigidity = rigidityMap.get(f) match {
            case Some(value) => value
            case None => if (rigidityDefaultExists) rigidityMap.default(f) else throw new EmbeddingException(s"Rigidity of symbol '$f' not defined and no default rigidity specified. Aborting.")
          }
          rigidity match {
            case Rigid =>
              val vars = boundVars ++ unboundVars0.zip(Seq.fill(unboundVars0.length)(metaFormulaType)).toMap
              (worldAbstraction(convertedArgs, vars),unboundVars)
            case Flexible => (convertedArgs,unboundVars)
          }

        case THF.Variable(variable) =>
          // create a map that holds both bound and unbound variables so a safe name can be generated for worlds
          val vars = boundVars ++ unboundVars0.zip(Seq.fill(unboundVars0.length)(metaFormulaType)).toMap
          // if the variable is bound, do a world abstraction to make type correct
          if (boundVars.keySet.contains(variable)) (worldAbstraction(formula, vars), unboundVars0)
          else {
            // otherwise add variable to the sequence of unbound variables and return variable without world abstraction
            // since the type will be assigned type mworld > $o in meta logic formula quantification later on
            val unboundVars = if (!unboundVars0.contains(variable)) unboundVars0 :+ variable else unboundVars0
            (formula, unboundVars)
          }

        case THF.NonclassicalPolyaryFormula(connective, args) =>
          if (args.size == 1) {
            val body = args.head
            val unboundVars = convertSyntacticPreFormula(body,boundVars,unboundVars0,specIndex)._2
            val convertedBody = convertSyntacticPreFormula(body,boundVars,unboundVars,specIndex)._1
            val convertedConnective: THF.Formula = connective match {
              case THF.NonclassicalBox(index) => index match {
                case Some(index0) => specIndex match {
                  case Some(_) =>
                    // when specIndex is given, the formula is used to define a modal operator in multimodal logic spec
                    // test weather the index given to the operator is the same as the index of the modal operator it is used to define in the logic-spec
                    if (escapeModalIndex(index0)==specIndex.get) mboxIndexed(index0)
                    else throw new EmbeddingException(s"Index of Modal Operator #${index0.pretty} in Modal Spec doesn't match the Index (${unescapeTPTPName(specIndex.get.pretty)}) it defines.")
                  case None =>
                    // when no specIndex is given, the formula is a meta axiom and given index can be used
                    mboxIndexed(index0)
                }
                case None => specIndex match {
                  case Some(value) =>
                    // when specIndex is given, the formula is used to define a modal operator in multimodal logic spec
                    // in this case, assign the index of the defined operator in the logic spec to unindexed operators in formulas
                    THF.BinaryFormula(THF.App, mbox, value)
                  case None => str2Fun("mbox")
                }
              }
              case THF.NonclassicalDiamond(index) => index match {
                case Some(index0) => specIndex match {
                  case Some(_) =>
                    if (escapeModalIndex(index0)==specIndex.get) mdiaIndexed(index0)
                    else throw new EmbeddingException(s"Index of Modal Operator <#${index0.pretty}> in Modal Spec doesn't match the Index (${specIndex.get}) it defines.")
                  case None =>
                    mdiaIndexed(index0)
                }
                case None => specIndex match {
                  case Some(value) =>
                    THF.BinaryFormula(THF.App, mdia, value)
                  case None => str2Fun("mdia")
                }
              }
              case THF.NonclassicalLongOperator(name, index, parameters) =>
                if (parameters.nonEmpty) throw new EmbeddingException(s"Only up to one index is allowed in box operator, but parameters '${parameters.toString()}' was given.")
                name match {
                  case x if synonymsForBox.contains(x) => index match {
                      case Some(index0) => specIndex match {
                        case Some (value) => if (escapeModalIndex(index0) == value) mboxIndexed (index0)
                           else throw new EmbeddingException (s"Index of Modal Operator ${connective.pretty} in Modal Spec doesn't match the Index (${value.pretty}) it defines.")
                        case None => mboxIndexed(index0)
                      }
                      case None => specIndex match {
                        case Some(value) => THF.BinaryFormula(THF.App, mbox, value)
                        case None => str2Fun("mbox")
                      }
                  }
                  case x if synonymsForDiamond.contains(x) => index match {
                    case Some(index0) => specIndex match {
                      case Some(value) => if (escapeModalIndex(index0) == value) mdiaIndexed(index0)
                        else throw new EmbeddingException(s"Index of Modal Operator ${connective.pretty} in Modal Spec doesn't match the Index ${value.pretty} it defines.")
                      case None => mdiaIndexed(index0)
                    }
                    case None => specIndex match {
                      case Some(value) => THF.BinaryFormula(THF.App, mdia, value)
                      case None => str2Fun("mdia")
                    }
                  }
                  case "$forbidden" => index match {
                    case Some(index0) => specIndex match {
                      case Some(value) => if (escapeModalIndex(index0) == value) {
                        val box = mboxIndexed(index0)
                        modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                      } else throw new EmbeddingException(s"Index of Modal Operator ${connective.pretty} in Modal Spec doesn't match the Index ${value.pretty} it defines.")
                      case None =>
                        val box = mboxIndexed(index0)
                        modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                    }
                    case None => specIndex match {
                        case Some(value) =>
                          val box = THF.BinaryFormula(THF.App, mbox, value)
                          modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                        case None =>
                          val box = str2Fun("mbox")
                          modules.input.TPTPParser.thf(s"^[Phi: $worldTypeName > $$o]: (${box.pretty} @ (mnot @ Phi))")
                      }
                  }
                  case _ => throw new EmbeddingException(s"Unknown connective name '$name'.")
                }
              case _ => throw new EmbeddingException(s"Unsupported non-classical operator: '${connective.pretty}'")
            }
            (THF.BinaryFormula(THF.App, convertedConnective, convertedBody),unboundVars)
          } else {
            throw new EmbeddingException(s"Only unary operators supported in modal embedding, but '${formula.pretty}' was given.")
          }

        case THF.BinaryFormula(connective, left, right) =>
          val unboundVars = convertSyntacticPreFormula(left, boundVars, unboundVars0, specIndex)._2 ++ convertSyntacticPreFormula(right, boundVars, unboundVars0, specIndex)._2
          val convertedLeft: TPTP.THF.Formula = convertSyntacticPreFormula(left, boundVars, unboundVars, specIndex)._1
          val convertedRight: TPTP.THF.Formula = convertSyntacticPreFormula(right, boundVars, unboundVars, specIndex)._1
          // create map containing all Variables to also take into account unbound variables when creating safe names
          val vars = boundVars ++ unboundVars.zip(Seq.fill(unboundVars.length)(metaFormulaType)).toMap
          val safeName = generateSafeName(vars)
          val appliedLeft = THF.BinaryFormula(THF.App, convertedLeft, THF.Variable(safeName))
          val appliedRight = THF.BinaryFormula(THF.App, convertedRight, THF.Variable(safeName))
          (worldAbstraction(THF.BinaryFormula(connective, appliedLeft, appliedRight), safeName),unboundVars)

        case THF.UnaryFormula(connective, body) =>
          /* In theory, this could be rewritten to an application of body to a constant.
             But this results in a ugly formula, because TPTP has a dedicated syntax for unary formulas.
             So we replace the result of doing this with an identical expression that uses a nicer syntax */
          val unboundVars = convertSyntacticPreFormula(body, boundVars, unboundVars0, specIndex)._2
          val convertedBody: TPTP.THF.Formula = convertSyntacticPreFormula(body, boundVars, unboundVars, specIndex)._1
          val vars = boundVars ++ unboundVars.zip(Seq.fill(unboundVars.length)(metaFormulaType)).toMap
          val safeName = generateSafeName(vars) // a name that is not free in the formula
          val appliedBody = THF.BinaryFormula(THF.App, convertedBody, THF.Variable(safeName))
          (worldAbstraction(THF.UnaryFormula(connective, appliedBody), safeName),unboundVars)

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          /* in theory, this could be rewritten to a lambda applied to a constant.
             But this results in a ugly formula, because TPTP has a dedicated syntax for quantifications.
             So we replace the result of doing this with an identical expression that uses a nicer syntax */
          val updatedBoundVars = boundVars.concat(variableList)
          val unboundVars = convertSyntacticPreFormula(body, updatedBoundVars, unboundVars0, specIndex)._2
          val convertedBody = convertSyntacticPreFormula(body, updatedBoundVars, unboundVars, specIndex)._1
          val vars = boundVars ++ unboundVars.zip(Seq.fill(unboundVars.length)(metaFormulaType)).toMap
          val safeName = generateSafeName(vars) // a name that is not free in the formula
          val appliedBody: THF.Formula = THF.BinaryFormula(App, convertedBody, THF.Variable(safeName))
          // Step through variables one-by-one to allow introducing exists-in-world-predicates
          val result = variableList.foldRight(appliedBody)(mkSingleQuantified(quantifier, safeName))
          (worldAbstraction(result, safeName),unboundVars)

        case THF.ConnectiveTerm(_) =>
          val vars = boundVars ++ unboundVars0.zip(Seq.fill(unboundVars0.length)(metaFormulaType)).toMap
          (worldAbstraction(formula, vars),unboundVars0) // connectives are rigid: so do a world abstraction

        // TPTP special cases BEGIN
        case THF.Tuple(elements) =>
          val unboundVars = elements.flatMap(convertSyntacticPreFormula(_, boundVars, unboundVars0, specIndex)._2)
          val convertedElements: Seq[TPTP.THF.Formula] = elements.map(convertSyntacticPreFormula(_, boundVars, unboundVars, specIndex)._1)
          (THF.Tuple(convertedElements),unboundVars)

        case THF.ConditionalTerm(condition, thn, els) =>
          val unboundVars = convertSyntacticPreFormula(condition, boundVars, unboundVars0, specIndex)._2 ++ convertSyntacticPreFormula(thn, boundVars, unboundVars0, specIndex)._2 ++ convertSyntacticPreFormula(els, boundVars, unboundVars0, specIndex)._2
          val convertedCondition: TPTP.THF.Formula = convertSyntacticPreFormula(condition, boundVars, unboundVars, specIndex)._1
          val convertedThn: TPTP.THF.Formula = convertSyntacticPreFormula(thn, boundVars, unboundVars, specIndex)._1
          val convertedEls: TPTP.THF.Formula = convertSyntacticPreFormula(els, boundVars, unboundVars, specIndex)._1
          val vars = boundVars ++ unboundVars.zip(Seq.fill(unboundVars.length)(metaFormulaType)).toMap
          val safeName = generateSafeName(vars) // a name that is not free in the formula
          val appliedCond = THF.BinaryFormula(THF.App, convertedCondition, THF.Variable(safeName))
          val appliedThn = THF.BinaryFormula(THF.App, convertedThn, THF.Variable(safeName))
          val appliedEls = THF.BinaryFormula(THF.App, convertedEls, THF.Variable(safeName))
          (worldAbstraction(THF.ConditionalTerm(appliedCond, appliedThn, appliedEls), safeName),unboundVars)

        case THF.LetTerm(_, _, _) => // Treat new symbols like bound variables // TODO
          throw new EmbeddingException("TPTP let statements currently not supported. Aborting.")
        // TPTP special cases END

        /* Remaining cases are:
        *  - THF.DefinedTH1ConstantTerm(_)
        *  - THF.DistinctObject(_)
        *  - THF.NumberTerm(_).
        * They are all the same (rigid constants). */
        case _ =>
          val vars = boundVars ++ unboundVars0.zip(Seq.fill(unboundVars0.length)(metaFormulaType)).toMap
          (worldAbstraction(formula, vars),unboundVars0)
      }
    }

    private def quantifySyntacticPreFormula(formula: THF.Formula, unboundVars: Seq[String]): THF.Formula = {
      // the free variables given in syntactic formulas in the logic spec are treated as meta-logic formulas
      // therefore, quantification over the wohle given formula is added and free variables are assigned type mworld > $o
      val res = unboundVars match {
        case Seq() =>
          THF.BinaryFormula(THF.App,str2Fun("mglobal"),formula)
        case _ =>
          val metaFormulaType = THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), THF.FunctionTerm(s"$$o", Seq.empty))
          THF.QuantifiedFormula(THF.!,Seq((unboundVars.distinct.mkString(", "),metaFormulaType)),THF.BinaryFormula(THF.App,str2Fun("mglobal"),formula))
      }
      res
    }

    private def convertSemanticPreFormula(formula: THF.Formula, specIndex: Option[TPTP.THF.FunctionTerm]): THF.Formula = {
      formula match{
        case THF.Variable(_) =>
          // variables occurring in semantic formulas in logic spec are necessarily of type mworld
          formula

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          var convertedVariables: Seq[(String, THF.Type)] = Seq.empty
          variableList foreach {
            case (variableName,THF.FunctionTerm("$ki_world",Seq())) =>
              // change "$ki:world" to "mworld"
              convertedVariables = convertedVariables :+ (variableName, str2Fun(worldTypeName))
            case (variableName,variableType) =>
              throw new EmbeddingException(s"Invalid type '${variableType.pretty}' of $variableName: In semantic formulas in the logic spec, quantification is only allowed over variables of type ki_world")
         }
          val convertedBody:THF.Formula = convertSemanticPreFormula(body,specIndex)
          THF.QuantifiedFormula(quantifier,convertedVariables, convertedBody)

        case THF.FunctionTerm(f,args) => f match{
          case "$accessible_world" => specIndex match {
            // change "$accessible_world" to "mrel"
            // no index of the accessibility relation being defined can be given to "$accessible_world" in semantic formulas so the index of the modal operator that the formula characterizes in the logic spec is used for "mrel"
            case Some(value) =>
              val rel = THF.BinaryFormula(THF.App, str2Fun("mrel"), value)
              if (args.nonEmpty) THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, rel, args.head), args.last)
              else THF.FunctionTerm(rel.pretty, args)
            case None =>
              val rel = s"(mrel)"
              if (args.nonEmpty) THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, str2Fun(rel), args.head), args.last)
              else THF.FunctionTerm(rel, args)
          }
          case otherName =>
            throw new EmbeddingException(s"Invalid function or predicate in semantic in the logic spec: $otherName given but only $$accessible_world is allowed")
        }

        case THF.BinaryFormula(connective,left,right) =>
          val convertedLeft: THF.Formula = convertSemanticPreFormula(left,specIndex)
          val convertedRight: THF.Formula = convertSemanticPreFormula(right,specIndex)
          THF.BinaryFormula(connective, convertedLeft, convertedRight)

        case THF.UnaryFormula(connective,body) =>
          val convertedBody: THF.Formula = convertSemanticPreFormula(body,specIndex)
          THF.UnaryFormula(connective, convertedBody)

        case otherFormula =>
          throw new EmbeddingException(s"Invalid Symbol ${otherFormula.pretty} in semantic formulas of logic spec")
      }
    }

    @inline private[this] def mbox: THF.Formula = str2Fun("mbox")
    private[this] def mboxIndexed(index: THF.Formula): THF.Formula = THF.BinaryFormula(THF.App, mbox, multiModal(index))
    @inline private[this] def mdia: THF.Formula = str2Fun("mdia")
    private[this] def mdiaIndexed(index: THF.Formula): THF.Formula = THF.BinaryFormula(THF.App, mdia, multiModal(index))

    @inline private[this] def worldAbstraction(body: THF.Formula, boundVars: Map[String, THF.Type]): THF.Formula =
      THF.QuantifiedFormula(THF.^, Seq((generateSafeName(boundVars), THF.FunctionTerm(worldTypeName, Seq.empty))), body)
    @inline private[this] def worldAbstraction(body: THF.Formula, name: String): THF.Formula =
      THF.QuantifiedFormula(THF.^, Seq((name, THF.FunctionTerm(worldTypeName, Seq.empty))), body)

    private def mkSingleQuantified(quantifier: THF.Quantifier, worldName: String)(variable: THF.TypedVariable, acc: THF.Formula): THF.Formula = {
      val variableType = variable._2
      quantifierType(variableType)
      try {
        if (domainMap(variableType.pretty) == ConstantDomain) THF.QuantifiedFormula(quantifier, Seq(variable), acc)
        else {
          /* with exists-in-world guard */
          val eiwPredicate = if (polymorphic) "eiw" else s"eiw_${serializeType(variableType)}"
          val appliedEiw = THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, str2Fun(eiwPredicate), THF.Variable(variable._1)), THF.Variable(worldName))
          val convertedBody = quantifier match {
            case THF.! => THF.BinaryFormula(THF.Impl, appliedEiw, acc)
            case THF.? => THF.BinaryFormula(THF.&, appliedEiw, acc)
            case _ => acc
          }
          THF.QuantifiedFormula(quantifier, Seq(variable), convertedBody)
        }
      } catch {
        case _:NoSuchElementException => throw new EmbeddingException(s"Domain semantics for type '${variable._2.pretty}' not defined; and no default semantics specified. Aborting.")
      }
    }

    private def getRigidityOfSymbol(name: String, typ: THF.Type): Rigidity = {
      rigidityMap.get(name) match {
        case Some(value) => value
        case None =>
          val goal: TPTP.THF.Type = goalType(typ)
          goal match { // Special treatment for formulas/predicates: flexible by default
            case THF.FunctionTerm("$o", Seq()) => Flexible
            case _ => if (rigidityDefaultExists) rigidityMap.default(name) else throw new EmbeddingException(s"Rigidity of symbol '$name' not defined and no default rigidity specified. Aborting.")
          }
      }
    }

    @inline private[this] def generateSafeName(boundVars: Map[String, THF.Type]): String = generateFreshTPTPVariableName("W", boundVars.keySet)

    private def convertTypeFormula(formula: TPTP.THFAnnotated): AnnotatedFormula = {
      formula.formula match {
        case THF.Typing(symbol, typ) =>
          val rigidity = getRigidityOfSymbol(symbol, typ)
          rigidityMap = rigidityMap + (symbol -> rigidity) // add to table in case it was implicit (e.g. a predicate)
          val convertedType = convertConstantSymbolType(symbol, typ)
          reverseSymbolTypeMap = reverseSymbolTypeMap + (convertedType -> (reverseSymbolTypeMap(convertedType) + symbol))
          val convertedTyping = TPTP.THF.Typing(symbol, convertedType)
          TPTP.THFAnnotated(formula.name, formula.role, convertedTyping, formula.annotations)
        case _ => throw new EmbeddingException(s"Malformed type definition in formula '${formula.name}', aborting.")
      }
    }

    private def convertConstantSymbolType(symbol: String, typ: TPTP.THF.Type): TPTP.THF.Type = {
      val rigidity = getRigidityOfSymbol(symbol, typ)
      worldTypeLiftBasedOnRigidity(typ, rigidity)
    }

    @inline private[this] def worldTypeLiftBasedOnRigidity(typ: THF.Type, rigidity: Rigidity): THF.Type =
      rigidity match {
        case Rigid => typ
        case Flexible => THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), typ)
      }

    ///////////////////////////////////////////////////
    // Local embedding state
    ///////////////////////////////////////////////////
    // For warnings that should go inside the output file
    private[this] val warnings: mutable.Buffer[String] = mutable.Buffer.empty

    private[this] var localFormulaExists = false
    private[this] var globalFormulaExists = false

    private[this] val modalOperators: mutable.Set[THF.FunctionTerm] = mutable.Set.empty
    private[this] def isMultiModal: Boolean = modalOperators.nonEmpty
    private[this] def multiModal(index: THF.Formula): THF.FunctionTerm = {
      val index0 = escapeModalIndex(index)
      modalOperators += index0
      index0
    }
    private[this] var isS5 = false // True iff mono-modal and modality is S5

    private[this] def escapeModalIndex(index: THF.Formula): THF.FunctionTerm = index match {
        case THF.FunctionTerm(name, args) => THF.FunctionTerm(s"'#$name'", args)
        case THF.NumberTerm(TPTP.Integer(value)) => THF.FunctionTerm(s"'#$value'", Seq.empty)
        case _ => throw new EmbeddingException(s"Unsupported index '${index.pretty}'")
      }

    private[this] val quantifierTypes: mutable.Set[THF.Type] = mutable.Set.empty
    private[this] def quantifierType(typ: THF.Type): Unit = {
      quantifierTypes += typ
    }

    /* All the meta formulas that move BEFORE user-type definitions. */
    private def generateMetaPreFormulas(): Seq[AnnotatedFormula] = {
      import scala.collection.mutable
      import modules.input.TPTPParser.annotatedTHF
      val result: mutable.Buffer[AnnotatedFormula] = mutable.Buffer.empty

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
      // Then: Define modal operators
      if (isMultiModal) result.appendAll(indexedModalOperatorsTPTPDef())
      else result.appendAll(simpleModalOperatorsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Give mrel properties
      var indexSpecificFormulas: Seq[AnnotatedFormula] = Seq.empty
      var generalMetaFormulas:Seq[THFAnnotated] = Seq.empty
      if (isMultiModal) {
        val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) indexedSemanticAxiomTable else indexedSyntacticAxiomTable
        modalOperators foreach { index =>
          /////////////////////////////////////////////////////////////
          // Predefined axiom schemes (sem/syn)
          // write used properties and assign (if semantical)
          // or write syntactical axioms (if syntactical)
          val modalSystem = modalsMapPredefined.get(index) match {
            case Some(value) => value
            case None => if (modalDefaultExists) modalsMapPredefined.default(index) else throw new EmbeddingException(s"Modal properties for index '${index.pretty}' not defined; and no default properties specified. Aborting.")
          }
          val axiomNames = if (isModalSystemName(modalSystem.head)) modalSystemTable(modalSystem.head) else modalSystem
          axiomNames foreach { ax =>
            val axiom = axiomTable.apply(ax)
            axiom.foreach { f =>
              val res = f(index)
              indexSpecificFormulas = indexSpecificFormulas :+ res
            }
          }
          /////////////////////////////////////////////////////////////
          // Semantic and syntactic formulas
          // index of the operator the formulas define in the logic-spec is used to assign correct index to operators given without index
          // and to check weather operators given with an index are indexed correctly
          var SemanticFormulaCount: Int = 0
          var SyntacticFormulaCount: Int = 0
          modalsMapFormulas.get(index) foreach { formulaList =>
            formulaList foreach { formula =>
              def isSemantic: Boolean = formula.symbols.contains("$accessible_world")
              // convert semantic logic-spec formulas
              if (isSemantic) {
                // count formulas in order to enumerate them
                SemanticFormulaCount = SemanticFormulaCount +1
                val convertedFormula = convertSemanticPreFormula(formula, Some(index))
                val annotatedSemantic = annotatedTHF(s"thf('mrel_${unescapeTPTPName(index.pretty)}_semantic$SemanticFormulaCount', axiom, ${convertedFormula.pretty} ).")
                indexSpecificFormulas = indexSpecificFormulas :+ annotatedSemantic
              }
              // convert syntactic logic-spec formulas
              else {
                // count formulas in order to enumerate them
                SyntacticFormulaCount = SyntacticFormulaCount +1
                val convertedFormula = convertSyntacticPreFormula(formula,Map.empty,Seq.empty,Some(index))
                val quantifiedFormula = quantifySyntacticPreFormula(convertedFormula._1,convertedFormula._2)
                val annotatedSyntactic = annotatedTHF(s"thf('mrel_${unescapeTPTPName(index.pretty)}_syntatic$SyntacticFormulaCount', axiom, ${quantifiedFormula.pretty} ).")
                indexSpecificFormulas = indexSpecificFormulas :+ annotatedSyntactic
              }
            }
          }
        }
      } else {
        /////////////////////////////////////////////////////////////
        // Predefined axiom schemes in mono-modal case
        val modalSystemOrAxiomNameList = if (modalDefaultExists) modalsMapPredefined.default(THF.FunctionTerm("*dummy*", Seq.empty)) else throw new EmbeddingException(s"Modal operator properties not specified. Aborting.")
        val axiomNames = if (isModalSystemName(modalSystemOrAxiomNameList.head)) {
          val systemName = modalSystemOrAxiomNameList.head
          if (systemName == "$modal_system_S5") {
            isS5 = true
          }
          modalSystemTable(modalSystemOrAxiomNameList.head)
        } else modalSystemOrAxiomNameList
        val axiomTable = if (modalityEmbeddingType == MODALITY_EMBEDDING_SEMANTICAL) semanticAxiomTable else syntacticAxiomTable
        val modalAxioms = axiomNames.flatMap(axiomTable).toSet
        result.appendAll(modalAxioms)
      }
      /////////////////////////////////////////////////////////////
      // Bridge axioms and other meta axioms
      var SemanticFormulaCount: Int = 0
      var InteractionSchemeCount: Int = 0
      var GeneralAxiomSchemeCount: Int = 0
      modalsMetaAxioms foreach {axiom =>
        def isSemantic: Boolean = axiom.symbols.contains("$accessible_world")
        // In the multimodal case, semantic formulas can not be given outside the definitions for specific modal operators right now since the syntax does not allow for it.
        // In the monomodal case, semantic formulas can be given here and represent the general characteristics of the (only) accessibility relation.
        if (isSemantic & isMultiModal) throw new EmbeddingException(s"Semantic notation for meta axioms and bridge axioms is not supported in the multimodal case, so ${axiom.pretty} can not be embedded")
        else if (isSemantic & !isMultiModal){
          SemanticFormulaCount = SemanticFormulaCount + 1
          val convertedMetaFormula = convertSemanticPreFormula(axiom, None)
          val annotatedAxiom = annotatedTHF(s"thf('semantic_condition_$SemanticFormulaCount', axiom, ${convertedMetaFormula.pretty} ).")
          generalMetaFormulas = generalMetaFormulas :+ annotatedAxiom
          }
        else {
          // if formulas are not semantic, they are either interaction schemes or other general axiom schemes
          // extract the indices that were given in the formulas to classify formula
          val convertedMetaFormula = convertSyntacticPreFormula(axiom, Map.empty, Seq.empty, None)
          val quantifiedMetaFormula = quantifySyntacticPreFormula(convertedMetaFormula._1, convertedMetaFormula._2)
          val indices = quantifiedMetaFormula.symbols.intersect(modalOperators.map(_.pretty))
          // if no indices were given, the formula is a general axiom scheme
          if (indices.isEmpty & !isMultiModal) {
            GeneralAxiomSchemeCount = GeneralAxiomSchemeCount + 1
            val annotatedAxiom = annotatedTHF(s"thf('axiom_scheme_$GeneralAxiomSchemeCount', axiom, ${quantifiedMetaFormula.pretty} ).")
            generalMetaFormulas = generalMetaFormulas :+ annotatedAxiom
          }
          // in the multimodal case, the formula has to be given for each of the operators
          else if (indices.isEmpty & isMultiModal) {
            GeneralAxiomSchemeCount = GeneralAxiomSchemeCount + 1
            modalOperators.foreach { index =>
              val convertedMetaFormulaIndexSpecific = convertSyntacticPreFormula(axiom, Map.empty, Seq.empty, Some(index))
              val quantifiedMetaFormulaIndexSpecific = quantifySyntacticPreFormula(convertedMetaFormulaIndexSpecific._1, convertedMetaFormulaIndexSpecific._2)
              val annotatedAxiom = annotatedTHF(s"thf('mrel_${unescapeTPTPName(unescapeTPTPName(index.pretty))}_axiom_scheme_$GeneralAxiomSchemeCount', axiom, ${quantifiedMetaFormulaIndexSpecific.pretty} ).")
              generalMetaFormulas = generalMetaFormulas :+ annotatedAxiom
            }
          }
          // if exactly one index was used, the formula should be given as a definition for the specific operator and not as a general axiom scheme
          else if (indices.size == 1) {
            throw new EmbeddingException(s"The formula ${quantifiedMetaFormula.pretty} was given as a general axiom scheme but only defines one modal operator used in the problem: ${indices.head}. Give formula as an operator specific axiom scheme instead.")
          }
          // if more than one index was given, formula is an interaction scheme
          if (indices.size > 1) {
            InteractionSchemeCount = InteractionSchemeCount + 1
            val annotatedAxiom = annotatedTHF(s"thf('interaction_scheme_$InteractionSchemeCount', axiom, ${quantifiedMetaFormula.pretty} ).")
            generalMetaFormulas = generalMetaFormulas :+ annotatedAxiom
          }
        }
      }
      /////////////////////////////////////////////////////////////
      // Then: Define mglobal/mlocal
      if (localFormulaExists) {
        result.appendAll(mlocalTPTPDef())
      }
      if (globalFormulaExists ||
        modalityEmbeddingType == MODALITY_EMBEDDING_SYNTACTICAL || // We use mglobal for those meta-definitions
        domainEmbeddingType == DOMAINS_EMBEDDING_SYNTACTICAL ||
        generalMetaFormulas.nonEmpty) { // and for syntactic formulas and meta axioms of logic-spec
        result.appendAll(mglobalTPTPDef()) // so introduce mglobal also if there is no global object-level formula
      }
      /////////////////////////////////////////////////////////////
      // Then: append the formulas given in the logic-spec
      result.appendAll(indexSpecificFormulas)
      result.appendAll(generalMetaFormulas)

      result.toSeq
    }

    /* All the meta formulas that move AFTER user-type definitions. */
    private def generateMetaPostFormulas(): Seq[AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[AnnotatedFormula] = mutable.Buffer.empty

      /////////////////////////////////////////////////////////////
      // Define exist-in-world-predicates and quantifier restrictions (if cumul/decr/vary)
      try {
        if (polymorphic) {
          if (quantifierTypes.nonEmpty) {
            if (quantifierTypes.exists(ty => domainMap(ty.pretty) != ConstantDomain)) {
              result.appendAll(polyIndexedExistsInWorldTPTPDef()) // define poly eiw
              if (!allowEmptyDomains) result.appendAll(polyIndexedExistsInWorldNonEmptyTPTPDef()) // domain non-empty
              quantifierTypes.foreach { ty => // postulate existence for each constant symbol of that type (if any),
                // or, if S5 and cumul/decreasing, then as universal predicate
                if (isS5 && (domainMap(ty.pretty) == CumulativeDomain || domainMap(ty.pretty) == DecreasingDomain)) {
                  result.appendAll(polyIndexedUniversalExistsInWorldTPTPDef(ty))
                } else {
                  if (localExtension) {
                    reverseSymbolTypeMap(ty).foreach { constant =>
                      result.appendAll(polyIndexedConstantExistsInWorldTPTPDef(ty, constant))
                    }
                  }
                }
              }
            }
            if (domainEmbeddingType == DOMAINS_EMBEDDING_SEMANTICAL) {
              quantifierTypes foreach { ty =>
                if (domainMap(ty.pretty) == CumulativeDomain && !isS5)
                  result.appendAll(polyIndexedCumulativeExistsInWorldTPTPDef(ty)) // define cumul axioms for eiw with that type
                if (domainMap(ty.pretty) == DecreasingDomain && !isS5)
                  result.appendAll(polyIndexedDecreasingExistsInWorldTPTPDef(ty)) // define decreasing axioms for eiw with that type
              }
            } else {
              // in case of syntactical embedding: write restrictions using CBF resp. BF now.
              quantifierTypes foreach { ty =>
                if (domainMap(ty.pretty) == CumulativeDomain && !isS5) {
                  result.appendAll(indexedConverseBarcanFormulaTPTPDef(ty))
                } else if (domainMap(ty.pretty) == DecreasingDomain && !isS5) {
                  result.appendAll(indexedBarcanFormulaTPTPDef(ty))
                }
              }
            }
          }
        } else {
          quantifierTypes foreach { ty =>
            if (domainMap(ty.pretty) != ConstantDomain) {
              result.appendAll(indexedExistsInWorldTPTPDef(ty)) // define eiw with standard axioms
              if (!allowEmptyDomains) result.appendAll(indexedExistsInWorldNonEmptyTPTPDef(ty)) // domain non-empty
              if (domainMap(ty.pretty) != VaryingDomain && isS5) {
                // Special case: If cumul or decreasing, and in S5, then it's equivalent to constant domain.
                // Simulate this by postulating eiw as constant true (simpler to do, implementation wise, than removing eiw completely)
                result.appendAll(indexedUniversalExistsInWorldTPTPDef(ty))
              } else {
                if (localExtension) {
                  reverseSymbolTypeMap(ty).foreach { constant => // postulate existence for each constant symbol of that type (if any)
                    result.appendAll(indexedConstantExistsInWorldTPTPDef(ty, constant))
                  }
                }
              }
            }
            // In case of non-S5, add cumul/decreasing axioms
            if (domainEmbeddingType == DOMAINS_EMBEDDING_SEMANTICAL) {
              if (domainMap(ty.pretty) == CumulativeDomain && !isS5)
                result.appendAll(indexedCumulativeExistsInWorldTPTPDef(ty)) // define cumul axioms for eiw
              else if (domainMap(ty.pretty) == DecreasingDomain && !isS5)
                result.appendAll(indexedDecreasingExistsInWorldTPTPDef(ty)) // define decreasing axioms for eiw
            } else {
              // in case of syntactical embedding: write restrictions using CBF resp. BF now.
              if (domainMap(ty.pretty) == CumulativeDomain && !isS5) {
                result.appendAll(indexedConverseBarcanFormulaTPTPDef(ty))
              } else if (domainMap(ty.pretty) == DecreasingDomain && !isS5) {
                result.appendAll(indexedBarcanFormulaTPTPDef(ty))
              }
            }
          }
        }
      } catch {
        case _:NoSuchElementException => throw new EmbeddingException(s"Domain semantics for some type not defined; and no default semantics specified. Aborting.")
      }
      /////////////////////////////////////////////////////////////
      // Return all
      result.toSeq
    }

    ///////////////////////////////////////////////////
    // TPTP definitions relevant for the embedding
    ///////////////////////////////////////////////////

    @inline private[this] def worldTypeName: String = "mworld"
    @inline private[this] def indexTypeName: String = "mindex"

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(${worldTypeName}_type, type, $worldTypeName: $$tType).")
    }
    private[this] def indexTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(${indexTypeName}_type, type, $indexTypeName: $$tType).")
    }

    private[this] def indexTPTPDef(index: THF.FunctionTerm): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      val name = s"${unescapeTPTPName(index.pretty)}_decl"
      annotatedTHF(s"thf(${escapeName(name)}, type, ${index.pretty}: $indexTypeName).")
    }

    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_decl, type, mrel: $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def indexedAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_decl, type, mrel: $indexTypeName > $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def mglobalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mglobal_decl, type, mglobal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mglobal_def, definition, mglobal = (^ [Phi: $worldTypeName > $$o]: ![W: $worldTypeName]: (Phi @ W)) ).")
      )
    }

    private[this] def mlocalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mactual_decl, type, mactual: $worldTypeName)."),
        annotatedTHF(s"thf(mlocal_decl, type, mlocal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mlocal_def, definition, mlocal = (^ [Phi: $worldTypeName > $$o]: (Phi @ mactual)) ).")
      )
    }

    private[this] def simpleModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_decl, type, mbox: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_decl, type, mdia: ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def indexedModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_decl, type, mbox: $indexTypeName > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [R:$indexTypeName, Phi:$worldTypeName>$$o,W:$worldTypeName]: ! [V:$worldTypeName]: ( (mrel @ R @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_decl, type, mdia: $indexTypeName > ($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [R:$indexTypeName, Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ R @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def indexedExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_decl, type, eiw_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o))."),
      )
    }
    private[this] def indexedExistsInWorldNonEmptyTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_nonempty, axiom, ![W:$worldTypeName]: ?[X:${typ.pretty}]: (eiw_${serializeType(typ)} @ X @ W) ).")
      )
    }
    private[this] def indexedUniversalExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(typ)}_universal, axiom, ![W:$worldTypeName]: ![X:${typ.pretty}]: (eiw_${serializeType(typ)} @ X @ W) ).")
      )
    }
    private[this] def indexedConstantExistsInWorldTPTPDef(typ: THF.Type, name: String): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf('eiw_${serializeType(typ)}_${unescapeTPTPName(name)}_exists', axiom, ![W:$worldTypeName]: (eiw_${serializeType(typ)} @ ${escapeAtomicWord(name)} @ W) ).")
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
        annotatedTHF(s"thf(eiw_decl, type, eiw: !>[T:$$tType]: (T > $worldTypeName > $$o)).")
      )
    }
    private[this] def polyIndexedExistsInWorldNonEmptyTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(eiw_nonempty, axiom, ![T:$$tType, W:$worldTypeName]: ?[X:T]: (eiw @ T @ X @ W) ).")
      )
    }
    private[this] def polyIndexedUniversalExistsInWorldTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf('eiw_${unescapeTPTPName(name)}_universal', axiom, ! [W:$worldTypeName]: ![X:${typ.pretty}]: (eiw @ ${typ.pretty} @ X @ W) ).")
      )
    }
    private[this] def polyIndexedConstantExistsInWorldTPTPDef(typ: THF.Type, name: String): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf('eiw_${unescapeTPTPName(name)}_exists', axiom, ![W:$worldTypeName]: (eiw @ ${typ.pretty} @ ${escapeAtomicWord(name)} @ W) ).")
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

    private[this] lazy val semanticAxiomTable: Map[String, Option[TPTP.AnnotatedFormula]] = {
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
    private[this] lazy val syntacticAxiomTable: Map[String, Option[TPTP.AnnotatedFormula]] = {
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

    private[this] lazy val indexedSyntacticAxiomTable: Map[String, Option[THF.Formula => TPTP.AnnotatedFormula]] = {
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

    private[this] lazy val indexedSemanticAxiomTable: Map[String, Option[THF.Formula => TPTP.AnnotatedFormula]] = {
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

    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////

    private[this] def createState(spec: TPTP.AnnotatedFormula): Unit = {
      assert(spec.role == "logic")
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(name, Seq()),THF.Tuple(spec0))) if allowedModalLogicNames contains name =>
          spec0 foreach {
            case THF.BinaryFormula(THF.==, THF.FunctionTerm(propertyName, Seq()), rhs) =>
              propertyName match {
                case `logicSpecParamNameTermLocality` =>
                  warnings.append(s"Parameter '$logicSpecParamNameTermLocality' currently unsupported; this will probably coincide with global terms.")
                case `logicSpecParamNameRigidity` =>
                  val (default, map) = parseTHFSpecRHS(rhs)
                  if (default.isDefined) { rigidityDefaultExists = true }
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
                  val (default, map) = parseTHFSpecRHS(rhs)
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
                      case "$constant" => domainMap += (name -> ConstantDomain)
                      case "$varying" => domainMap += (name -> VaryingDomain)
                      case "$cumulative" => domainMap += (name -> CumulativeDomain)
                      case "$decreasing" => domainMap += (name -> DecreasingDomain)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$quantification'")
                    }
                  }
                case `logicSpecParamNameModalities` => val (default, mapPredefined, mapFormulas, metaAxioms) = parseTHFModalSpecRHS(rhs)
                  if (default.nonEmpty) {
                    modalDefaultExists = true
                    if (default.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec))) {
                      modalsMapPredefined = modalsMapPredefined.withDefaultValue(default)
                    } else throw new EmbeddingException(s"Unknown modality specification: ${default.mkString("[", ",", "]")}")
                  }
                  mapPredefined foreach { case (lhs, modalspec) =>
                    val index0 = lhs match {
                      case THF.NonclassicalPolyaryFormula(THF.NonclassicalBox(Some(index)), Seq()) => index
                      case THF.NonclassicalPolyaryFormula(THF.NonclassicalLongOperator(cname, Some(index), Seq()), Seq())
                       if synonymsForBox.contains(cname) => index
                      case _ => throw new EmbeddingException(s"Modality specification did not start with '[#idx] == ...' or '{#box(#idx)} == ...'.")
                    }
                    val index = escapeModalIndex(index0)
                    if (modalspec.nonEmpty) {
                      if (modalspec.forall(spec => isModalSystemName(spec) || isModalAxiomName(spec))) {
                        modalsMapPredefined = modalsMapPredefined + (index -> modalspec)
                      } else throw new EmbeddingException(s"Unknown modality specification: ${modalspec.mkString("[", ",", "]")}")
                    }
                  }
                  mapFormulas foreach { case (lhs, modalspec) =>
                    val index0 = lhs match {
                      case THF.NonclassicalPolyaryFormula(THF.NonclassicalBox(Some(index)), Seq()) => index
                      case THF.NonclassicalPolyaryFormula(THF.NonclassicalLongOperator(cname, Some(index), Seq()), Seq())
                        if synonymsForBox.contains(cname) => index
                      case _ => throw new EmbeddingException(s"Modality specification did not start with '[#idx] == ...' or '{#box(#idx)} == ...'.")
                    }
                    val index = escapeModalIndex(index0)
                    if (modalspec.nonEmpty) {
                      modalsMapFormulas = modalsMapFormulas + (index -> modalspec)
                    }
                  }
                  modalsMetaAxioms = metaAxioms
                case _ => throw new EmbeddingException(s"Unknown modal logic semantics property '$propertyName'")
              }
            case s => throw new EmbeddingException(s"Malformed logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

  // Check if the logic spec contains interactions or other meta-axioms/-properties.
  private[this] def testSpecForExtendedEntries(spec: TPTP.AnnotatedFormula): Boolean = {
    import leo.modules.tptputils.SyntaxTransform.transformAnnotatedFormula
    val specTHF = transformAnnotatedFormula(TPTP.AnnotatedFormula.FormulaType.THF, spec)
    var result = false
    specTHF.formula match {
      case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(name, Seq()), THF.Tuple(spec0))) if Seq("$modal", "$alethic_modal", "$deontic_modal", "$epistemic_modal") contains name =>
        spec0 foreach {
          case THF.BinaryFormula(THF.==, THF.FunctionTerm("$modalities", Seq()), rhs) =>
            val (_, _, mapFormulas, metaAxioms) = parseTHFModalSpecRHS(rhs)
            if (mapFormulas.nonEmpty || metaAxioms.nonEmpty) result = true
          case _ => () // NOP
        }
        result
      case _ => false
    }
  }

}
