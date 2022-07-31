package leo
package modules
package embeddings

import datastructures.TPTP
import TPTP.{AnnotatedFormula, TFF, TFFAnnotated}


object NormativeDSLEmbedding extends Embedding {

  object NormativeDSLEmbeddingParameter extends Enumeration { }

  override final type OptionType = NormativeDSLEmbeddingParameter.type

  override final val name: String = "$$normative"
  override final val version: String = "1.1"
  override final def embeddingParameter: NormativeDSLEmbeddingParameter.type = NormativeDSLEmbeddingParameter

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =  {
    import leo.modules.input.TPTPParser.annotatedTHF
    val spec: StringBuilder = new StringBuilder
    spec.append("thf(logic_spec, logic, (")
    spec.append(s"$name == [")
    spec.append("$$logic == ")
    specs.get("$$logic") match {
      case Some(value) => spec.append(value)
      case None => throw new EmbeddingException("Not enough logic specification parameters given.")
    }
    spec.append("] )).")
    annotatedTHF(spec.toString)
  }

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[NormativeDSLEmbeddingParameter.Value]): TPTP.Problem =
    new NormativeDSLEmbeddingImpl(problem).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class NormativeDSLEmbeddingImpl(problem: TPTP.Problem) {

    sealed abstract class TargetLogicFormalism
    final case object SDL extends TargetLogicFormalism
    final case object AqvistE extends TargetLogicFormalism
    final case object CarmoJones extends TargetLogicFormalism
    private[this] var targetLogic: Option[TargetLogicFormalism] = None

    def apply(): TPTP.Problem = {
      val formulas = problem.formulas

      val (spec, otherFormulas) = splitTFFInput(formulas)
      createState(spec)
      if (targetLogic.isEmpty) throw new EmbeddingException("Translation not possible as the logic specification did not specify" +
        "the target logic system to be used.")
      val convertedFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedLogicSpec: Seq[AnnotatedFormula] = generateTargetLogicSpec()

      val result = generatedLogicSpec ++ convertedFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }

    def convertAnnotatedFormula(annotatedFormula: TFFAnnotated): TFFAnnotated = {
      annotatedFormula.formula match {
        case TFF.Logical(f) =>
          val convertedFormula = convertFormula(f)
          TPTP.TFFAnnotated(annotatedFormula.name, annotatedFormula.role, TPTP.TFF.Logical(convertedFormula), annotatedFormula.annotations)
        case _ => annotatedFormula
      }
    }

    private[this] def convertFormula(formula: TPTP.TFF.Formula): TPTP.TFF.Formula = {
      formula match {
        case f@TFF.NonclassicalPolyaryFormula(_, _) =>
          targetLogic.get match {
            case SDL => convertNCLFormulaToSDL(f)
            case AqvistE | CarmoJones => convertNCLFormulaToDDL(f)
          }

        case TFF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedBody = convertFormula(body)
          TFF.QuantifiedFormula(quantifier, variableList, convertedBody)
        case TFF.UnaryFormula(connective, body) =>
          val convertedBody = convertFormula(body)
          TFF.UnaryFormula(connective, convertedBody)
        case TFF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertFormula(left)
          val convertedRight = convertFormula(right)
          TFF.BinaryFormula(connective, convertedLeft, convertedRight)
        case TFF.ConditionalFormula(condition, thn, els) =>
          val convertedCondition = convertFormula(condition)
          val convertedThn = convertTerm(thn)
          val convertedEls = convertTerm(els)
          TFF.ConditionalFormula(convertedCondition, convertedThn, convertedEls)
        case TFF.LetFormula(typing, binding, body) =>
          val convertedBinding = binding.map{ case (l,r) => (convertTerm(l), convertTerm(r))}
          val convertedBody = convertTerm(body)
          TFF.LetFormula(typing, convertedBinding, convertedBody)

        case TFF.Equality(left, right) => TFF.Equality(convertTerm(left), convertTerm(right))
        case TFF.Inequality(left, right) => TFF.Inequality(convertTerm(left), convertTerm(right))

        case TFF.AtomicFormula(_, _) | TFF.FormulaVariable(_)  => formula

        case _ => throw new EmbeddingException(s"Unsupported formula in conversion: '${formula.pretty}'. ")
      }
    }

    private[this] def convertTerm(term: TPTP.TFF.Term): TPTP.TFF.Term = term

    private[this] def convertNCLFormulaToSDL(formula: TFF.NonclassicalPolyaryFormula): TFF.Formula = {
      formula.connective match {
        case f@TFF.NonclassicalLongOperator(name, parameters) =>
          val targetIndex: Option[TFF.Term] = parameters match {
            case Seq() => None
            case Seq(Right((TFF.AtomicTerm("bearer", Seq()), idx))) => Some(idx)
            case _ => throw new EmbeddingException(s"Unexpected parameters in NCL connective '${f.pretty}'.")
          }
          name match {
            case "$$obligation" => formula.args match {
              case Seq(left, right) => TFF.BinaryFormula(TFF.Impl, left, TFF.NonclassicalPolyaryFormula(TFF.NonclassicalBox(targetIndex), Seq(right)))
              case Seq(body) => TFF.BinaryFormula(TFF.Impl, TFF.AtomicFormula("$true", Seq.empty), TFF.NonclassicalPolyaryFormula(TFF.NonclassicalBox(targetIndex), Seq(body)))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$prohibition" => formula.args match {
              case Seq(left, right) => TFF.BinaryFormula(TFF.Impl, left, TFF.NonclassicalPolyaryFormula(TFF.NonclassicalBox(targetIndex), Seq(TFF.UnaryFormula(TFF.~, right))))
              case Seq(body) => TFF.BinaryFormula(TFF.Impl, TFF.AtomicFormula("$true", Seq.empty), TFF.NonclassicalPolyaryFormula(TFF.NonclassicalBox(targetIndex), Seq(TFF.UnaryFormula(TFF.~, body))))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$permission" => formula.args match {
              case Seq(left, right) => TFF.BinaryFormula(TFF.Impl, left, TFF.NonclassicalPolyaryFormula(TFF.NonclassicalDiamond(targetIndex), Seq(right)))
              case Seq(body) => TFF.BinaryFormula(TFF.Impl, TFF.AtomicFormula("$true", Seq.empty), TFF.NonclassicalPolyaryFormula(TFF.NonclassicalDiamond(targetIndex), Seq(body)))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$constitutive" => formula.args match {
              case Seq(left, right) => TFF.BinaryFormula(TFF.Impl, left, right)
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
          }
        case _ => throw new EmbeddingException(s"Unexpected NCL expression '${formula.pretty}'.")
      }
    }

    @inline private val dsdlObligationConnectiveName: String = "$$obl"
    @inline private val dsdlBoxConnectiveName: String = "$$box"
    private[this] def convertNCLFormulaToDDL(formula: TFF.NonclassicalPolyaryFormula): TFF.Formula = {
      formula.connective match {
        case f@TFF.NonclassicalLongOperator(name, parameters) =>
          parameters match {
            case Seq() => ()
            case Seq(Right((TFF.AtomicTerm("bearer", Seq()), _))) => throw new EmbeddingException(s"Bearer annotation not supported in DSDL: '${f.pretty}'.")
            case _ => throw new EmbeddingException(s"Unexpected parameters in NCL connective '${f.pretty}'.")
          }
          name match {
            case "$$obligation" => formula.args match {
              case Seq(precondition, obligation) => TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(obligation,precondition))
              case Seq(obligation) => TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(obligation, TFF.AtomicFormula("$true", Seq.empty)))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$prohibition" => formula.args match {
              case Seq(precondition, prohibition) => TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(TFF.UnaryFormula(TFF.~, prohibition), precondition))
              case Seq(prohibition) => TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(TFF.UnaryFormula(TFF.~, prohibition), TFF.AtomicFormula("$true", Seq.empty)))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$permission" => formula.args match {
              case Seq(precondition, permission) => TFF.UnaryFormula(TFF.~, TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(TFF.UnaryFormula(TFF.~, permission),precondition)))
              case Seq(permission) => TFF.UnaryFormula(TFF.~, TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlObligationConnectiveName, Seq.empty), Seq(TFF.UnaryFormula(TFF.~, permission),TFF.AtomicFormula("$true", Seq.empty))))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
            case "$$constitutive" => formula.args match {
              case Seq(left, right) => TFF.NonclassicalPolyaryFormula(TFF.NonclassicalLongOperator(dsdlBoxConnectiveName, Seq.empty), Seq(TFF.BinaryFormula(TFF.Impl, left, right)))
              case _ => throw new EmbeddingException(s"NCL expression '${formula.pretty}' with unexpected number of arguments.")
            }
          }
        case _ => throw new EmbeddingException(s"Unexpected NCL expression '${formula.pretty}'.")
      }
    }

    private[this] def generateTargetLogicSpec(): Seq[TFFAnnotated] = {
      import input.TPTPParser.annotatedTFF
      val spec = targetLogic.get match {
        case SDL => annotatedTFF("tff(target_logic, logic, $modal == [$quantification == $constant, $constants == $rigid, $modalities == $modal_system_D]).")
        case AqvistE => annotatedTFF("tff(target_logic, logic, $$ddl == [$$system == $$aqvistE]).")
        case CarmoJones => annotatedTFF("tff(target_logic, logic, $$ddl == [$$system == $$carmoJones]).")
      }
      Seq(spec)
    }

    private[this] def createState(spec: TPTP.TFFAnnotated): Unit = {
      spec.formula match {
        case TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(`name`, Seq()), TFF.Tuple(spec0))) =>
          spec0 foreach {
            case TFF.FormulaTerm(TFF.MetaIdentity(TFF.AtomicTerm(propertyName, Seq()), rhs)) =>
              propertyName match {
                case "$$logic" => rhs match {
                  case TFF.AtomicTerm(value, Seq()) =>
                    value match {
                      case "$$sdl" => targetLogic = Some(SDL)
                      case "$$aqvistE" => targetLogic = Some(AqvistE)
                      case "$$carmoJones" => targetLogic = Some(CarmoJones)
                      case _ => throw new EmbeddingException(s"Unknown property value '$value' for property '$propertyName' in logic specification ${spec.pretty}")
                    }
                  case _ => throw new EmbeddingException(s"Malformed property value '${rhs.pretty}' for property '$propertyName' in logic specification ${spec.pretty}")
                }
                case _ => throw new EmbeddingException(s"Unknown logic semantics property '$propertyName'")
              }
            case line => throw new EmbeddingException(s"Malformed entry '${line.pretty}' in logic specification ${spec.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }
  }
}
