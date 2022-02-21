package leo.modules.embeddings


import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, THF}

object DHOLEmbedding extends Embedding {
  object DHOLEmbeddingParameter extends Enumeration { }
  /** The type of parameter options provided by the embedding instance. */
  override type OptionType = DHOLEmbeddingParameter.type

  /** The name of the embedding */
  override def name: String = "$$dhol"

  /** The version number of the embedding instance implementation. */
  override def version: String = "1.0"

  /** The enumeration object of this embedding's parameter values. */
  override def embeddingParameter: DHOLEmbeddingParameter.type = DHOLEmbeddingParameter

  /** Given the specification `specs` construct a valid TPTP logic specification for the logic
   * targeted by this embedding. */
  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =  {
    import leo.modules.input.TPTPParser.annotatedTHF
    val spec: StringBuilder = new StringBuilder
    spec.append("thf(logic_spec, logic, (")
    spec.append(s"$name == [")
    spec.append("$$system == ")
    specs.get("$$system") match {
      case Some(value) => spec.append(value)
      case None => throw new EmbeddingException("Not enough logic specification parameters given.")
    }
    spec.append("] )).")
    annotatedTHF(spec.toString)
  }

  override def apply(problem: TPTP.Problem, embeddingOptions: Set[DHOLEmbeddingParameter.Value]): TPTP.Problem =
    new DHOLEmbeddingImpl(problem).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class DHOLEmbeddingImpl(problem: TPTP.Problem) {
    def apply(): TPTP.Problem = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val formulas = problemTHF.formulas
      val (spec, properFormulas) = splitInput(formulas)

      val (typeFormulas, nonTypeFormulas) = properFormulas.partition(_.role == "type")
      val (definitionFormulas, otherFormulas) = nonTypeFormulas.partition(_.role == "definition")
      val convertedTypeFormulas = typeFormulas.flatMap(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val boolPred = TPTP.THFAnnotated(typePredName("bool"), "definition",
        THF.Logical(THF.BinaryFormula(THF.Eq, atomicTerm(typePredName("bool")),
          THF.QuantifiedFormula(THF.^, Seq(("X", bool)), atomicTerm("$true")))), None)

      val result = Seq(boolPred) ++ convertedTypeFormulas ++ convertedDefinitionFormulas ++ convertedOtherFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }


    /**
     * Translate the body of the definition formula
     * @param formula the definition formula to convert
     * @return the definition formula with the body translated with the convertFormula function
     */
    def convertDefinitionFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), body)), annotations) =>
          TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, atomicTerm(symbolName), convertFormula(body))), annotations)
        case _ => throw new EmbeddingException(s"Unsupported definition formula: ${formula.pretty}")
      }
    }

    /**
     * Translate the formula contained in an annotated formula
     * @param formula the contained formula
     * @return the annotated formula with the contained formula translated by the convertFormula function
     */
    def convertAnnotatedFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Logical(formula), annotations) =>
          TPTP.THFAnnotated(name, role, TPTP.THF.Logical(convertFormula(formula)), annotations)
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private[this] def convertFormula(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
      import TPTP.THF.App

      formula match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertFormula)
          THF.FunctionTerm(f, convertedArgs)

        case THF.UnaryFormula(connective, body) =>
          THF.UnaryFormula(connective, convertFormula(body))

        case THF.BinaryFormula(conn, left, right) =>
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(conn, convertedLeft, convertedRight)

        case THF.ConnectiveTerm(_) => formula

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedVariableList = variableList map {
            case (str, tp) => (str, convertType(tp))
          }
          val convertedBody = convertFormula(body)

          def relativizeVar(v: (String, THF.Type), body: THF.Formula) = v match {
            case (str, tp) => THF.BinaryFormula(THF.Impl, typePred(tp, THF.Variable(str)), body)
          }

          lazy val relativizedBody = variableList.foldRight(convertedBody)(relativizeVar)
          quantifier match {
            case THF.! => THF.QuantifiedFormula(THF.!, convertedVariableList, relativizedBody)
            case THF.? => THF.QuantifiedFormula(THF.?, convertedVariableList, relativizedBody)
            case _ => THF.QuantifiedFormula(quantifier, convertedVariableList, convertedBody)
          }

        case v: THF.Variable => v
        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    private def atomicTerm(s:String): THF.Formula = THF.FunctionTerm(s, Seq.empty)
    private val bool = atomicTerm("$o")
    private val univTp = atomicTerm("$tType")
    private def FuncType(A: THF.Formula, B:THF.Formula) = THF.BinaryFormula(THF.FunTyConstructor, A, B)

    private def convertPi(variableList: Seq[(String, THF.Type)], ret: THF.Type): THF.Type= {
      def convertFunType(v: (String, THF.Type), body: THF.Type): THF.Type = v match {
        case (_, tp) => FuncType(convertType(tp), convertType(body))
      }
      variableList.foldRight(ret)(convertFunType)
    }

    private def convertTypeFormula(formula: AnnotatedFormula): Seq[AnnotatedFormula] = {
      formula match {
        // Normalize nested pi-types to simplify the subsequent logic
        case TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl, THF.QuantifiedFormula(THF.!>, vl2, bdy))), an) =>
          convertTypeFormula(TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl++vl2, bdy)), an))
        case TPTP.THFAnnotated(name, "type", TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedType = convertType(typ)
          var declType: THF.Type = univTp
          val type_pred = typ match {
            // A generic type declaration
            case THF.QuantifiedFormula(THF.!>, variableList, ret) if (ret == univTp) =>
              val tp = convertPi(variableList,
                FuncType(atomicTerm(symbol), bool))
              TPTP.THFAnnotated(typePredName(symbol), "type", TPTP.THF.Typing(typePredName(symbol), tp), annotations)
            // special case of a type declaration with no arguments
            case THF.FunctionTerm("$tType", Seq()) =>
              val tp = FuncType(atomicTerm(symbol), bool)
              TPTP.THFAnnotated(typePredName(symbol), "type", TPTP.THF.Typing(typePredName(symbol), tp), annotations)
            // This is a term declaration
            case _ =>
              declType = convertedType
              TPTP.THFAnnotated(axName(symbol), "axiom",
                THF.Logical(typePred(typ,atomicTerm(symbol))), annotations)
          }
          val convertedTyping = TPTP.THF.Typing(symbol, declType)
          val convertedFormula = TPTP.THFAnnotated(name, "type", convertedTyping, annotations)
          Seq(convertedFormula, type_pred)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }
    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, args) => THF.FunctionTerm(f, Seq.empty)
        case THF.QuantifiedFormula(THF.!>, variableList, body) => convertPi(variableList, convertType(body))
        case _ => typ
      }
    }
    private def typePred(typ: THF.Formula, tm: THF.Formula): THF.Formula = {
      typ match {
        case THF.FunctionTerm(f, args) => THF.FunctionTerm(typePredName(f), args.map(convertFormula).appended(tm))
        case THF.QuantifiedFormula(THF.!>, vl, body) => vl.toList match {
          case (x,tp)::variableList =>
            val convertedTp = convertType(tp)
            val bodyTp = THF.QuantifiedFormula(THF.!>, variableList, body)
              THF.QuantifiedFormula(THF.!, Seq((x, convertedTp)), THF.BinaryFormula(THF.Impl,
                typePred(tp, TPTP.THF.Variable(x)), typePred(bodyTp, THF.BinaryFormula(THF.App, tm, THF.Variable(x)))))
          case Nil => typePred(body, tm)
        }
        // TODO: This code is apparently unreachable, but it shouldn't
        case THF.FunctionTerm("$o", args) if args.isEmpty => atomicTerm(typePredName("bool"))
        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${typ.pretty}'")
      }
    }
    private def typePredName(f:String): String = f+"_pred"
    private def axName(f:String): String = f+"_tp_ax"
  }
}
