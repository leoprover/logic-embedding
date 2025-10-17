package leo.modules.embeddings

import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, THF}
import leo.datastructures.TPTP.THF.FunctionTerm

import scala.annotation.tailrec

/** @author Colin Rothgang, Daniel Renalter */
object DHOLEmbedding extends Embedding {
  import DHOLEmbeddingUtils._
  var constants : List[(String, TPTP.THF.Type)] = Nil
  var simpleTypes : List[THF.Type] = Nil

  object DHOLEmbeddingParameter extends Enumeration { }
  /** The type of parameter options provided by the embedding instance. */
  override type OptionType = DHOLEmbeddingParameter.type

  /** The name of the embedding */
  override def name: String = "$$dhol"

  /** The version number of the embedding instance implementation. */
  override def version: String = "1.2.1"

  /** The enumeration object of this embedding's parameter values. */
  override def embeddingParameter: DHOLEmbeddingParameter.type = DHOLEmbeddingParameter

  /** Given the specification `specs` construct a valid TPTP logic specification for the logic
   * targeted by this embedding. */
  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =  {
    import leo.modules.input.TPTPParser.annotatedTHF
    annotatedTHF(s"thf(logic_spec, logic, $name).")
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
      val (_, properFormulas) = splitInput(formulas)

      val (typeFormulas, nonTypeFormulas) = properFormulas.partition(_.role == "type")
      val (definitionFormulas, otherFormulas) = nonTypeFormulas.partition(_.role == "definition")
      val convertedTypeFormulas = typeFormulas.flatMap(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)

      // Abbreviation for ((f @ a) @ b)
      def binaryApp(f: String, a: String, b: String): THF.BinaryFormula =
        THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, THF.FunctionTerm(f, Seq()), THF.FunctionTerm(a, Seq())),
          THF.FunctionTerm(b, Seq()))

      // The type of a PER of type A: A -> A -> bool
      val aao = THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm("A", Seq()),
              THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm("A", Seq()), bool))

      // Statements for the type of polymorphic PERs and their definition. This makes the rest of the translation significantly shorter
      val is_per_type = TPTP.THFAnnotated("is_per_type", "type",
        THF.Typing("isPer", THF.QuantifiedFormula(THF.!>, Seq(("A", THF.FunctionTerm("$tType", Seq()))),
          THF.BinaryFormula(THF.FunTyConstructor, aao, bool))), None)
      val aType = THF.FunctionTerm("A", Seq())

      val is_per_def = TPTP.THFAnnotated("is_per", "definition",
        THF.Logical(THF.QuantifiedFormula(THF.!, Seq(("A", THF.FunctionTerm("$tType", Seq())), ("AStar", aao)),
          THF.BinaryFormula(THF.<=>, binaryApp("isPer", "A", "AStar"),
            THF.BinaryFormula(THF.&,
              THF.QuantifiedFormula(THF.!, Seq(("X", aType), ("Y", aType)),
                THF.BinaryFormula(THF.Impl, binaryApp("AStar", "X", "Y"), binaryApp("AStar", "Y", "X"))),
              THF.QuantifiedFormula(THF.!, Seq(("X", aType), ("Y", aType), ("Z", aType)),
                THF.BinaryFormula(THF.Impl, binaryApp("AStar", "X", "Y"),
                  THF.BinaryFormula(THF.Impl, binaryApp("AStar", "Y", "Z"), binaryApp("AStar", "X", "Z")))))))), None)

      val result = List(is_per_type, is_per_def) ++ convertedTypeFormulas ++
        convertedDefinitionFormulas ++ convertedOtherFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }


    /**
     * Translate the body of the definition formula
     * @param formula the definition formula to convert
     * @return the definition formula with the body translated with the convertFormula function
     */
    def convertDefinitionFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, "definition", THF.Logical(f@(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), body))), annotations) =>
          val variables = collectVars(f)
          TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, atomicTerm(symbolName), convertFormula(body, variables))), annotations)
        case TPTP.THFAnnotated(name, "definition", THF.Logical(f@(THF.BinaryFormula(THF.<=>, THF.FunctionTerm(symbolName, Seq()), body))), annotations) =>
          val variables = collectVars(f)
          TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.<=>, atomicTerm(symbolName), convertFormula(body, variables))), annotations)
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
          val variables = collectVars(formula)
          TPTP.THFAnnotated(name, role, TPTP.THF.Logical(convertFormula(formula, variables)), annotations)
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private[this] def convertFormula(formula: TPTP.THF.Formula, variables: List[(String, TPTP.THF.Type)]): TPTP.THF.Formula = {
      formula match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(x => convertFormula(x, variables))
          THFApply(atomicTerm(f), convertedArgs)

        case THF.UnaryFormula(connective, body) =>
          THF.UnaryFormula(connective, convertFormula(body, variables))

        case THF.BinaryFormula(conn, left, right) =>
          val inferredLeftType = inferType(variables, constants)(left)
          val inferredRightType = inferType(variables, constants)(right)
          val convertedLeft = if (inferredLeftType == univTp) convertType(left, variables) else
            convertFormula(left, variables)
          val convertedRight = if (inferredRightType == univTp) convertType(right, variables) else
            convertFormula(right, variables)
          conn match {
            case THF.Eq | THF.Neq =>
              if (isSimpleType(inferredLeftType) && inferredLeftType == inferredRightType)
                THF.BinaryFormula(conn, convertedLeft, convertedRight)
              else
                relativizedEq(conn)(left, right)(variables)
            case _ => THF.BinaryFormula(conn, convertedLeft, convertedRight)
          }
        case THF.ConnectiveTerm(_) => formula
        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          if (List(THF.@+, THF.@-, THF.?*).contains(quantifier))
            throw new UnsupportedFragmentException("Unsupported quantifier: " + quantifier)
          else {
            variableList match {
              case (tp@(tpName, THF.FunctionTerm("$tType", Seq())))+:shorterList =>
                THF.QuantifiedFormula(quantifier, List(tp, (variableStar(tpName), genPerType(THF.FunctionTerm(tpName, Seq())))),
                  THF.BinaryFormula(THF.Impl,
                    THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, isPerPred, THF.FunctionTerm(tpName, Seq())),
                      THF.FunctionTerm(variableStar(tpName), Seq())),
                    convertFormula(THF.QuantifiedFormula(quantifier, shorterList, body), tp::variables)))
              case (tp@(_, THF.FunctionTerm("$o", Seq())))+:shorterList =>
                THF.QuantifiedFormula(quantifier, List(tp),
                  convertFormula(THF.QuantifiedFormula(quantifier, shorterList, body), tp::variables))
              case Nil => convertFormula(body, variables)
              case (fst@(tpvarname, tpname))+:shorterList =>
                if (onlyBooleans(tpname)) // Here we are only checking for booleans. It's probable that this simplification would work for any
                                          // non-dependent base type which would present optimization potential. But I have not formally investigated that.
                  THF.QuantifiedFormula(quantifier, List(fst),
                    convertFormula(THF.QuantifiedFormula(quantifier, shorterList, body), fst::variables))
                else {
                  val convertedVariableList = variableList map {
                    case (str, tp) => (str, normalizeNestedPi(convertType(tp, variables)))
                  }

                  val convertedBody = convertFormula(body, variableList.toList++variables)

                  def relativizeVar(connective: THF.BinaryConnective)(v: (String, THF.Type), body: THF.Formula) = v match {
                    case (str, tp@THF.FunctionTerm(n, _)) =>
                      body
                    case (str, tp) =>
                      THF.BinaryFormula(connective, typePred(tp, THF.Variable(str), variables), body)
                  }

                  def relativizedBody(connective: THF.BinaryConnective) = variableList.foldRight(convertedBody)(relativizeVar(connective))
                  quantifier match {
                    case THF.! => THF.QuantifiedFormula(THF.!, convertedVariableList, relativizedBody(THF.Impl))
                    case THF.? => THF.QuantifiedFormula(THF.?, convertedVariableList, relativizedBody(THF.&))
                    case _ => THF.QuantifiedFormula(quantifier, convertedVariableList, convertedBody)
                  }
                }
            }
          }

        case v: THF.Variable => v
        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    /**
      * Turn a dependent type into a simple one, i.e. \Pi x:A.B becomes A -> B
      * @param tp type to convert
      * @return simply typed analogue to the argument
      */
    private def convertPi(tp: THF.Type): THF.Type = {
      def innerConvertPi(variableList: Seq[(String, THF.Type)], ret: THF.Type): THF.Type = variableList match {
        case (_, tp)+:shorterList =>
          val body = THF.QuantifiedFormula(THF.!>, shorterList, ret)
          FuncType(tp, innerConvertPi(shorterList, ret))
        case Nil => ret
        case _ => throw new EmbeddingException("this should not happen:" +variableList)
      }
      tp match {
        case THF.QuantifiedFormula(THF.!>, varList, body) => innerConvertPi(varList, body)
        case _ =>  throw new EmbeddingException(s"convertPi Error - arg: " + tp.toString)
      }
    }

    /**
      * Generates a list of type variables needed to quantify over the translated type
      * @param tp The type for which to generate the variables
      * @param variables A list of present variables to avoid clashes
      * @return The list of variables that need to be quantified over
      */
    private def generatePolyVariables(tp: THF.Type, variables: List[THF.TypedVariable]): List[THF.TypedVariable] = tp match {
      case THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm("$tType", Seq()), right) =>
        val newVarName = generateFreshTPTPVariableName("A", (variables.map(x => x._1)).toSet)
        val newVar = (newVarName, THF.FunctionTerm("$tType", Seq()))
        newVar::generatePolyVariables(right, newVar::variables)
      case THF.BinaryFormula(THF.FunTyConstructor, _, right) =>
        generatePolyVariables(right, variables)
      case THF.FunctionTerm("$tType", Seq()) => Nil
    }


    /**
      * Adds the types needed as term arguments to the PER type
      * @param base The core of the PER e.g. list @ A > list @ A > $o for fixed-length lists
      * @param tp The type for which to add the remaining elements
      * @param variableList The list of variables for the type
      * @return The type of the PER e.g. (A > A > $o) > nat > list @ A > list @ A > $o for poly fixed-length lists
      */
    private def generateRelationType(base: THF.Type, tp: THF.Type, variableList: List[THF.TypedVariable]): THF.Type = {
      def TTO(name: String): THF.Type = {
        THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(name, Seq()),
          THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(name, Seq()), bool))
      }
      tp match {
        case THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm("$tType", Seq()), right) =>
          variableList match {
            case (v::vars) =>
              THF.BinaryFormula(THF.FunTyConstructor, TTO(v._1), generateRelationType(base, right, vars))
            case Nil =>  throw new EmbeddingException(s"generateRelatioNType: no vars left")
          }
        case THF.BinaryFormula(THF.FunTyConstructor, t, right) =>
          THF.BinaryFormula(THF.FunTyConstructor, convertType(t, variableList), generateRelationType(base, right, variableList))
        case THF.FunctionTerm("$tType", Seq()) =>
          base
        case x => throw new EmbeddingException(s"Error: " + x.toString)
      }
    }

    /** Generate the axiom that type typ is a PER
      * @param base The name of the symbol the PER is defined for
      * @param typ The type of the symbol the PER is defined for
      * @param typeVariableList A list of type variables accrued during creaton of the axiom
      * @param perVariableList A list of PER variables accrued during creaton of the axiom
      * @result An axiom stating that the PER over a symbol is indeed a PER
      */
    private def generateIsPerAxiom(base: String, typ: THF.Type, typeVariableList: List[THF.TypedVariable], perVariableList: List[THF.TypedVariable]): THF.Formula = {
      def TTO(name: String): THF.Type = {
        THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(name, Seq()),
          THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(name, Seq()), bool))
      }
      def IsPerInstance(left: THF.Formula, right: THF.Formula): THF.Formula =
        THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, isPerPred, left), right)
      typ match {
        case THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm("$tType", Seq()), right) =>
          val newVarName = generateFreshTPTPVariableName("B", (typeVariableList++perVariableList++constants).map(x => x._1).toSet)
          val newVar = THF.FunctionTerm(newVarName, Seq())
          val newVarPer = THF.FunctionTerm(variableStar(newVarName), Seq())
          THF.QuantifiedFormula(THF.!, Seq((newVarName, univTp), (variableStar(newVarName), TTO(newVarName))),
            THF.BinaryFormula(THF.Impl, IsPerInstance(newVar, newVarPer),
              generateIsPerAxiom(base, right, typeVariableList++List((newVarName, univTp)),
                perVariableList++List((newVarName, univTp), (variableStar(newVarName), TTO(variableStar(newVarName)))))))
        case THF.BinaryFormula(THF.FunTyConstructor, t, right) =>
          val newVarName = generateFreshTPTPVariableName("C", (typeVariableList++perVariableList++constants).map(x => x._1).toSet)
          val newVar = THF.FunctionTerm(newVarName, Seq())
          THF.QuantifiedFormula(THF.!, Seq((newVarName, convertType(t, typeVariableList++perVariableList))),
            generateIsPerAxiom(base, right, typeVariableList, perVariableList++List((newVarName, univTp))))
        case THF.FunctionTerm("$tType", Seq()) =>
          IsPerInstance(THFApply(THF.FunctionTerm(base, Seq()), typeVariableList.map(x => THF.FunctionTerm(x._1, Seq()))),
            THFApply(THF.FunctionTerm(variableStar(base), Seq ()), perVariableList.map(x => THF.FunctionTerm(x._1, Seq()))))
      }
    }

    private def convertType(typ: TPTP.THF.Type, variables: List[(String, TPTP.THF.Type)]): TPTP.THF.Type = {
      typ match {
        case THF.BinaryFormula(THF.FunTyConstructor, left, right) => if (left == THF.FunctionTerm("$tType", Seq())) { //Poly Extension
          THF.BinaryFormula(THF.FunTyConstructor, left, convertType(right, variables))
        } else {                             //Shallow Polymorphism only - once all typevars are gone, we can shortcut
          if (goalType(right) == univTp || right == univTp || isTypeDecl(typ)) {
            THF.FunctionTerm("$tType", Seq())
          } else {
            THF.BinaryFormula(THF.FunTyConstructor, convertType(left, variables), convertType(right, variables))
          }
        }
        case THF.FunctionTerm(f, _) => atomicTerm(f)
        case THF.BinaryFormula(THF.App, left, right) =>
          var inferredType: THF.Type = THF.FunctionTerm("",Seq())
          try {
            inferredType = inferType(variables, constants)(right)
          } catch {
            case e:EmbeddingException => { } //That probably shouldn't be a thing
          }
          if (inferredType == THF.FunctionTerm("$tType", Seq())) {
            THF.BinaryFormula(THF.App, convertType(left, variables), convertType(right, variables))
          } else {
            convertType(left, variables)
          }
        case f@THF.QuantifiedFormula(THF.!>, variableList, ret) => {
          variableList match {
            case (x, t@THF.FunctionTerm("$tType", Seq()))+:shorterList =>
              val body = THF.QuantifiedFormula(THF.!>, shorterList, ret)
              THF.QuantifiedFormula(THF.!>, Seq((x,t)), convertType(body, variables))
            case (y, q)+:shorterList =>
              if (isTypeDecl(f)) { //again because of shallow poly
                univTp
              } else {
                val body = THF.QuantifiedFormula(THF.!>, shorterList, ret)
                FuncType(convertType(q, variables), convertType(body, variables))
              }
            case Nil => convertType(ret, variables)
          }
        }
        case _ => typ
      }
    }

    /**
      * Turn Pi x:A Pi y:B.t into Pi x:a,y:B.t
      * @param formula The Pi to normalize
      * @result The normalized Pi
      */
    @tailrec
    private def normalizeNestedPi(formula: THF.Formula): THF.Formula = {
      formula match {
        case THF.QuantifiedFormula(THF.!>, vl, THF.QuantifiedFormula(THF.!>, vl2, bdy)) =>
          normalizeNestedPi(THF.QuantifiedFormula(THF.!>, vl++vl2, bdy))
        case _ => formula
      }
    }

    /**
      * Case distinction between simple and dependent types
      * @param formula The type formula to erase
      * @result The erased type formula + potential additional axioms about PERs etc
      */
    @tailrec
    private def convertTypeFormula(formula: AnnotatedFormula): List[AnnotatedFormula] = {
      formula match {
        // Normalize nested pi-types to simplify the subsequent logic
        case TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl, THF.QuantifiedFormula(THF.!>, vl2, bdy))), an) =>
          convertTypeFormula(TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl++vl2, bdy)), an))
        case TPTP.THFAnnotated(name, "type", TPTP.THF.Typing(symbol, typ), annotations) => typ match {
          case THF.QuantifiedFormula(THF.!>, _, _) =>
            convertTypeFormulaAux(formula)
          case THF.BinaryFormula(THF.FunTyConstructor, _, _) if (goalType(typ) == univTp) =>
            convertTypeFormulaAux(formula)
          case _ =>
            if (typ == univTp)
              simpleTypes +:= THF.FunctionTerm(symbol, Seq())
            convertTypeFormulaAux(formula)
        }
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    /**
      * Actual implementation of convertTypeFormula for non-simple types
      * This uses all the previous functions to piece together the erased formula, the typing statement for the PER as well as the axiom of (partial) equivalence
      * @param formula The type formula to erase
      * @result The erased type formula + potential additional axioms about PERs etc
      */
    private def convertTypeFormulaAux(formula: AnnotatedFormula): List[AnnotatedFormula] = formula match {
      case TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl, THF.QuantifiedFormula(THF.!>, vl2, bdy))), an) =>
        convertTypeFormula(TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl++vl2, bdy)), an))
      case TPTP.THFAnnotated(name, "type", TPTP.THF.Typing(symbol, typ), annotations) =>
        constants ::= (symbol, typ)
        var variables = collectVars(typ)
        val convertedType = normalizeNestedPi(convertType(typ, variables))
        var declType: THF.Type = convertedType
        val base = atomicTerm(symbol)
        def typeRelDecls(variableList: Seq[(String, THF.Type)], typetype: THF.Type): List[TPTP.THFAnnotated] = {
          val vars = generatePolyVariables(typetype, variables)
          variables = vars++variables
          val preDeclTp = if (vars == Nil) {
            THF.BinaryFormula(THF.FunTyConstructor, base,
              THF.BinaryFormula(THF.FunTyConstructor, base, bool))
          } else {
            THF.BinaryFormula(THF.FunTyConstructor, THFApply(base, vars.map(x => THF.FunctionTerm(x._1, Seq()))),
              THF.BinaryFormula(THF.FunTyConstructor, THFApply(base, vars.map(x => THF.FunctionTerm(x._1, Seq()))), bool))
          }
          val declTp = generateRelationType(preDeclTp, typetype, vars)
          val relationType = if (vars != Nil) {
            THF.QuantifiedFormula(THF.!>, vars, declTp)
          } else {
            declTp
          }
          val tpRelDecl = TPTP.THFAnnotated(unescapeTPTPName(typeRelName(symbol)), "type",
            TPTP.THF.Typing(typeRelName(symbol), relationType), annotations)

          val tpRelAx = if(isSimpleType(THF.FunctionTerm(symbol, Seq())))
            TPTP.THFAnnotated(unescapeTPTPName(typeRelName(symbol)) ++ "_is_eq", "axiom",
              THF.Logical(THF.QuantifiedFormula(THF.!, List(("X", THF.FunctionTerm(symbol, Seq())), ("Y", THF.FunctionTerm(symbol, Seq()))),
                THF.BinaryFormula(THF.<=>,
                  THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, THF.FunctionTerm(typeRelName(symbol), Seq()), THF.Variable("X")), THF.Variable("Y")),
                  THF.BinaryFormula(THF.Eq, THF.Variable("X"), THF.Variable("Y"))))), None)
          else
            TPTP.THFAnnotated(typeRelName(symbol) ++ "_is_per", "axiom",
              THF.Logical(generateIsPerAxiom(symbol, typetype, Nil, Nil)), None)
          List(tpRelDecl, tpRelAx)
        }
        val type_pred = typ match {
          // A generic type declaration
          case f@THF.QuantifiedFormula(THF.!>, variableList, _) if isTypeDecl(f) =>
            typeRelDecls(variableList, convertPi(f))
          case f@(THF.BinaryFormula(THF.FunTyConstructor, _, _)) if goalType(f) == univTp =>
            typeRelDecls(Nil, f)
          // special case of a type declaration with no arguments
          case f@THF.FunctionTerm("$tType", Seq())  => typeRelDecls(Nil, f) 
            // This is a term declaration
          case _ =>
            if (isSimpleType(typ)) {
              Nil
            } else {
              val tpPred = typePred(typ,base,variables) //fix type pred
              List(TPTP.THFAnnotated(axName(symbol), "axiom", THF.Logical(tpPred), annotations))
            }
        }
        val convertedTyping = TPTP.THF.Typing(symbol, declType)
        val convertedFormula = TPTP.THFAnnotated(name, "type", convertedTyping, annotations)
        convertedFormula::type_pred
    }

    /**
     * The following three functions are the most interesting part of the entire ambedding.
     * They describe which additional conditions we need to add to the translation to ensure it doesn't loose information.
     *
     * A similar translation would likely only noticeably differ in these functions
     */

    /**
     * Translate the (in)equality with equality symbol conn between left and right
     * @param conn either the equlity connective or the inequality connective
     * @param left the term on the left of the (in)equality
     * @param right the term on the right of the (in)equality
     * @param variables the free variable and their types
     * @return the "relativized" version of the (in)equality left (conn) right
     */
    private def relativizedEq(conn: THF.BinaryConnective)(left: THF.Formula, right: THF.Formula)(implicit variables: List[(String, TPTP.THF.Type)]) : THF.Formula = {
      val convertedLeft: TPTP.THF.Formula = convertFormula(left, variables)
      val convertedRight: TPTP.THF.Formula = convertFormula(right, variables)
      // in case of unsupported terms, type inference may fail
      val eqType = try {
        inferType(variables, constants)(left)
      } catch {
        case _: EmbeddingException =>
          try {
            inferType(variables, constants)(right)
          }
          catch {
            case _: EmbeddingException => throw new EmbeddingException(s"Failed to infer type of equality '${THF.BinaryFormula(conn, left, right)}'. ")
          }
      }
      conn match {
        case THF.Eq  => typeRel(eqType, convertedLeft, convertedRight, variables)
        case THF.Neq => THF.UnaryFormula(THF.~, typeRel(eqType, convertedLeft, convertedRight, variables))
        case _ => THF.BinaryFormula(conn, convertedLeft, convertedRight)
      }
    }
    /**
     * Generates the typing condition for the given type and term supposedly of that type
     * @param typ the type for which to generate the typing condition
     * @param tm the term for which to generate the typing condition
     * @return
     */
    private def typePred(typ: THF.Formula, tm: THF.Formula, variables: List[THF.TypedVariable]): THF.Formula = {
      def extendArg(trm: THF.Formula, tvar: THF.TypedVariable): THF.Formula = tvar match {//polymorphic extension
        case (x, THF.FunctionTerm("$tType", Seq())) => THF.BinaryFormula(THF.App, trm, THF.FunctionTerm(x, Seq()))
        case default => trm
      }
      typ match {
        case THF.QuantifiedFormula(THF.!>, variableList, body) =>
          val ntm = variableList.foldLeft(tm)(extendArg)
          typeRel(typ, ntm, ntm, variables)
        case _ =>
          typeRel(typ, tm, tm, variables)
      }
    }
    /**
     * Generates the typing condition, expands typing relations over Pi-types
     * @param typ the type of the typing relation
     * @param left the term on the left of the typing relation
     * @param right the term on the right of the typing relation
     * @return the typing relation for type typ applied to left and right
     */
    private def typeRel(typ: THF.Formula, left: THF.Formula, right: THF.Formula, varList: List[THF.TypedVariable]): THF.Formula = {
      def relAppl(tp: THF.FunctionTerm, left: THF.Formula, right: THF.Formula) = tp match {
        case THF.FunctionTerm(f, args) =>
          THFApply(atomicTerm(variableStar(f)), args.map(x => convertFormula(x, varList)).appendedAll(Seq(left, right)))
      }
      def typeRelApp(tp: THF.Formula):THF.Formula = tp match {
        case THF.BinaryFormula(THF.App, f, arg) =>
          var inferredType: THF.Type = THF.FunctionTerm("",Seq())
          inferredType = inferType(varList, constants)(arg)
          if (inferredType == univTp) {
            THFApply(typeRelApp(f), Seq(convertType(arg:THF.Type, varList),typeRelApp(arg:THF.Type)))
          } else {
            THFApply(typeRelApp(f), List(convertFormula(arg, varList)))
          }
        case THF.Variable(t) => atomicTerm(variableStar(t))
        case THF.FunctionTerm("$o", Seq()) => THF.BinaryFormula(THF.Eq, left, right)
        case THF.FunctionTerm(t, _) => atomicTerm(variableStar(t))
        case default => tp
      }

      def typeRelFuncType(x: String, tp: THF.Type, codomain: THF.Formula) = tp match {
        case THF.FunctionTerm(n, Seq()) if (n != "$tType") =>
          val leftAppl = THF.BinaryFormula(THF.App, left, THF.Variable(x))
          val rightAppl = THF.BinaryFormula(THF.App, right, THF.Variable(x))
          THF.QuantifiedFormula(THF.!, List((x, tp)), typeRel(codomain, leftAppl, rightAppl, (x, tp)+:varList))
        case _ =>
          val convertedTp = normalizeNestedPi(convertType(tp, varList))
          val vars = List((x, convertedTp), (primedName(x), convertedTp))
          val leftAppl = THF.BinaryFormula(THF.App, left, THF.Variable(x))
          val rightAppl = THF.BinaryFormula(THF.App, right, THF.Variable(primedName(x)))
          val innerEq = codomain match {
            case _ => typeRel(codomain, leftAppl, rightAppl, vars++varList)
          }

          THF.QuantifiedFormula(THF.!, vars,
            THF.BinaryFormula(THF.Impl, typeRel(tp, TPTP.THF.Variable(x), TPTP.THF.Variable(primedName(x)), vars++varList),
              innerEq))
      }
      typ match {
        case THF.FunctionTerm("$o", Seq()) => THF.BinaryFormula(THF.Eq, left, right)
        case f@THF.BinaryFormula(THF.App, _, _) => THFApply(typeRelApp(f), Seq(left, right)) 
        case f@THF.FunctionTerm(n, _) =>
          if (isSimpleType(f))
            THF.BinaryFormula(THF.Eq, left, right)
          else
            relAppl(f, left, right)
        case THF.BinaryFormula(THF.FunTyConstructor, tp, codomain)  => 
            val x = generateFreshTPTPVariableName("D", varList.map({v => v._1}).toSet)
            typeRelFuncType(x, tp, codomain)
        case THF.QuantifiedFormula(THF.!>, vl, body) => vl match {
          case (x,t@(THF.FunctionTerm("$tType", Seq())))+:variableList => //polymorphic extension
            val varName = generateFreshTPTPVariableName("E", ((varList++vl).map({v => v._1})).toSet)
            val xType = THF.FunctionTerm(x, Seq())
            val xStarType = THF.FunctionTerm(variableStar(x), Seq())
            val codomain = THF.QuantifiedFormula(THF.!>, variableList, body)
            val newBody = THF.BinaryFormula(THF.Impl, THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, isPerPred, xType), xStarType), typeRel(codomain, left, right, varList))
            THF.QuantifiedFormula(THF.!, Seq((x,t),(variableStar(x), genPerType(xType))), newBody)
          case (x,tp)+:variableList => 
            val codomain = THF.QuantifiedFormula(THF.!>, variableList, body)
            typeRelFuncType(x, tp, codomain)
          case Nil => typeRel(body, left, right, varList)
        }
        case x@THF.Variable(x1) if (inferType(varList, constants)(x) == univTp) =>
          typeRel(THF.FunctionTerm(x1, Seq()), left, right, varList)
        case _ => throw new EmbeddingException(s"Typing relation not defined on unsupported type '$name': '${typ.pretty}'")
      }
    }

    private def variableStar(vari: String): String = s"${vari}Star"
    private def typeRelName(f:String): String = s"'${unescapeTPTPName(f)}Star'"
    private def typeRelSymName(f:String): String = s"${unescapeTPTPName(typeRelName(f))}_sym"
    private def typeRelTransName(f:String): String = s"${unescapeTPTPName(typeRelName(f))}_trans"
    private def typeRelReduceName(f:String): String = s"${unescapeTPTPName(typeRelName(f))}_reduce"
    private def axName(f:String): String = unescapeTPTPName(f)+"_tp_ax"
    private def primedName(x: String) = unescapeTPTPName(x)+"_prime"
    private def genPerType(a: THF.Type) = THF.BinaryFormula(THF.FunTyConstructor, a, (THF.BinaryFormula(THF.FunTyConstructor, a, bool)))
    private def isPerPred = THF.FunctionTerm("isPer", Seq())

  }

  /**
    * Check if all types appearing in a type are Booleans.
    * This is only used in formulas, so there should not be any quantified types apearing (i hope)
    * @param tp The type to check
    * @result True iff only booleans appear as base types, otherwise false
    */
  private def onlyBooleans(tp: THF.Type) : Boolean = tp match {
    case THF.FunctionTerm("$o", Seq()) => true
    case THF.BinaryFormula(_, left, right) => onlyBooleans(left) && onlyBooleans(right)
    case THF.QuantifiedFormula(_, vl, body) => false
      // Note that in general, one could find a boolean function of form '!>[A:$o]: $o' so there is optimization potential here
    case _ => false
  }

  /**
    * Check if the argument is syntactically simple, i.e. no term dependence
    * Note that this does not check wether the argument of a Pi type occurs somewhere
    * i.e. a function type Pi x:A.B where B does not depend on A is not recognized as simple
    * @param tp The type to check
    * @result A boolean that is false if the provided type is non-simple
    */
  private def isSimpleType(tp: THF.Type) : Boolean = tp match {
    case THF.FunctionTerm("$o", Seq()) => true
    case THF.FunctionTerm(n, Seq()) => simpleTypes.exists(_ == tp)
    case THF.BinaryFormula(THF.FunTyConstructor, left, right) =>
      isSimpleType(left) && isSimpleType(right)
    case _ =>
      false
  }
}

object DHOLEmbeddingUtils {
  private[embeddings] def atomicTerm(s:String): THF.Formula = THF.FunctionTerm(s, Seq.empty)
  private[embeddings] val bool = atomicTerm("$o")
  private[embeddings] val univTp = atomicTerm("$tType")
  private[embeddings] def FuncType(A: THF.Formula, B:THF.Formula) = THF.BinaryFormula(THF.FunTyConstructor, A, B)

  /**
    * Replaces occurances of a variables or (constant) functions with a certain name with a arbitrary formula
    * @param formula The formula to replace in
    * @param replace A tuple (string, formula) where every occurance of 'string' is replaced by 'formula'
    * @return The input formula with instances replaced according to replace
    */
  private[embeddings] def variableReplace(formula: THF.Formula, replace: (String, THF.Formula)): THF.Formula = {
    def variableReplaceVarList(list: List[THF.TypedVariable], replace: (String, THF.Formula)): List[THF.TypedVariable] = list match {
      case h::t =>
        (h._1, variableReplace(h._2, replace))::variableReplaceVarList(t, replace)
      case Nil => Nil
    }
    formula match {
      case THF.UnaryFormula(c, f) =>
        THF.UnaryFormula(c, variableReplace(f, replace))
      case THF.BinaryFormula(c, l, r) =>
        THF.BinaryFormula(c, variableReplace(l, replace), variableReplace(r, replace))
      case THF.QuantifiedFormula(q, vl, f) =>
        THF.QuantifiedFormula(q, variableReplaceVarList(vl.toList, replace), variableReplace(f, replace))
      case f@THF.FunctionTerm(n, _) =>
        if (n == replace._1) {
          replace._2
        }
        else
          f
      case f@THF.Variable(n) =>
        if (n == replace._1)
          replace._2
        else
          f
      case _ =>
        throw new EmbeddingException("Unsupported formula to replace in: " + formula)
    }
  }

  /**
    * Traverses a formula and collects all quantified variables in a list
    * @param f The formula to traverse
    * @return A list of typed variables
    */
  private[embeddings] def collectVars(f: THF.Formula): List[THF.TypedVariable] = f match {
    case THF.QuantifiedFormula(_, variableList, body) => (variableList.toList)++collectVars(body)
    case THF.BinaryFormula(_, left, right) => collectVars(left) ++ collectVars(right)
    case THF.UnaryFormula(_, body) => collectVars(body)
    case _ => Nil
  }

  /**
    * Checks if a formula is a type declaration
    * @param f The formula to check
    * @return A boolean that is true iff the formula is a type declaration
    */
  private[embeddings] def isTypeDecl(f: THF.Formula):Boolean = f match {
    case THF.QuantifiedFormula(THF.!>, _, body) => isTypeDecl(body)
    case THF.BinaryFormula(THF.FunTyConstructor, _, right) => isTypeDecl(right)
    case THF.FunctionTerm("$tType", _) => true
    case _ => false
  }

  /** The application of function func to the arguments args */
  private[embeddings] def THFApply(func: THF.Formula, args: Seq[THF.Formula]): THF.Formula =
    args.foldLeft(func)({case (fappl, x) => THF.BinaryFormula(THF.App, fappl, x)})
  /**
   * Substitute the free variables from variableList in the term body by their definiens in replArgs
   * @param body the term to apply the substitution to
   * @param variableList the free variables to substitute
   * @param replArgs the terms to substitute for the free variables
   * @return
   */
  private[embeddings] def substituteVars(body: THF.Formula)(implicit variableList: Seq[(String, THF.Type)], replArgs: Seq[THF.Formula]): THF.Formula = {
    val varargs = variableList.take(replArgs.length).zip(replArgs)
    def substituteAtomic(name: String, default: THF.Formula) = {
      varargs.find(_._1._1 == name).map(_._2).getOrElse(default)
    }
    def substituteSubterm(tm: THF.Formula): THF.Formula = tm match {
      case v@THF.Variable(name) => substituteAtomic(name, v)
      case FunctionTerm(f, args) =>
        THFApply(substituteAtomic(f, FunctionTerm(f, Nil)), args.map(substituteSubterm).toList)
      case THF.QuantifiedFormula(quantifier, variableList, body) => THF.QuantifiedFormula(quantifier, variableList, substituteSubterm(body))
      case THF.UnaryFormula(connective, body) => THF.UnaryFormula(connective, substituteSubterm(body))
      case THF.BinaryFormula(connective, left, right) => THF.BinaryFormula(connective, substituteSubterm(left), substituteSubterm(right))
      case THF.Tuple(elements) => THF.Tuple(elements.map(substituteSubterm))
      case THF.ConditionalTerm(condition, thn, els) => THF.ConditionalTerm(substituteSubterm(condition), substituteSubterm(thn), substituteSubterm(els))
      case default => default
    }
    substituteSubterm(body)
  }

  /**
   * Infer the type of the given term from the types of the constants and variables in scope
   * @param formula the term whoose type to infer
   * @param variables the variables in the scope of the term
   * @param constants the constants
   * @return
   */
  private[embeddings] def inferType(variables: List[(String, TPTP.THF.Type)], constants: List[(String, TPTP.THF.Type)])(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
    @tailrec
    def applyNTp(tp: THF.Formula, args: Seq[THF.Formula]): THF.Formula = tp match {
      case THF.BinaryFormula(THF.FunTyConstructor, _, codomain) if args.length == 1 => codomain
      case THF.BinaryFormula(THF.FunTyConstructor, _, codomain) => applyNTp(codomain, args.tail)
      case THF.QuantifiedFormula(THF.!>, variableList, body) =>
        val substBody = substituteVars(body)(variableList, args)
        if (variableList.length == args.length) { substBody } else {
          THF.QuantifiedFormula(THF.!>, variableList.drop(args.length), substBody)
        }
    }
    def lookupAtomic(name: String) = (constants++variables).find(_._1 == name)
      .getOrElse(throw new EmbeddingException(s"Failed to look up variable or constant: "+name))._2
    def unsupportedFormula(): THF.Formula = throw new EmbeddingException(s"Not allowed on term level: "+formula.pretty)
    formula match {
      case THF.FunctionTerm("$true", _) => bool
      case THF.FunctionTerm("$false", _) => bool
      case THF.FunctionTerm(f, Nil) => lookupAtomic(f)
      case THF.FunctionTerm(f, args) =>
        applyNTp(inferType(variables, constants)(atomicTerm(f)), args)
      case THF.QuantifiedFormula(quantifier, variableList, body) => quantifier match {
        case THF.! | THF.? => bool
        case THF.^ => THF.QuantifiedFormula(THF.!>, variableList, inferType(variables, constants)(body))
        case default => throw new EmbeddingException(s"Unsupported on type level: "+default.pretty)
      }
      case THF.Variable(name) => lookupAtomic(name)
      case THF.UnaryFormula(THF.~, _) => bool
      case THF.BinaryFormula(connective, left, right) => connective match {
        case THF.App => applyNTp(inferType(variables, constants)(left), Seq(right))
        case THF.FunTyConstructor | THF.ProductTyConstructor | THF.SumTyConstructor =>
          throw new EmbeddingException(s"Not allowed on term level: "+connective.pretty)
        case _ => bool
      }
      case THF.Tuple(_) => unsupportedFormula()
      case THF.ConditionalTerm(_, thn, _) => inferType(variables, constants)(thn)
      case THF.LetTerm(_, _, _) => unsupportedFormula()
      case THF.DefinedTH1ConstantTerm(_) => unsupportedFormula()
      case THF.ConnectiveTerm(_) => unsupportedFormula()
      case THF.DistinctObject(_) => unsupportedFormula()
      case THF.NumberTerm(_) => unsupportedFormula()
    }
  }
}
