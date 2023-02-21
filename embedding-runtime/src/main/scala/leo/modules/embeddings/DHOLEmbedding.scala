package leo.modules.embeddings


import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, Annotations, THF}
import leo.datastructures.TPTP.THF.FunctionTerm

import scala.annotation.tailrec

object DHOLEmbedding extends Embedding {
  import DHOLEmbeddingUtils._
  var constants : List[(String, TPTP.THF.Type)] = Nil

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
      val (_, properFormulas) = splitInput(formulas)

      val (typeFormulas, nonTypeFormulas) = properFormulas.partition(_.role == "type")
      val (definitionFormulas, otherFormulas) = nonTypeFormulas.partition(_.role == "definition")
      val convertedTypeFormulas = typeFormulas.flatMap(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val boolPred = TPTP.THFAnnotated(typeRelName("bool"), "definition",
        THF.Logical(THF.BinaryFormula(THF.Eq, atomicTerm(typeRelName("bool")),
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

    private[this] def convertFormula(formula: TPTP.THF.Formula)(implicit variables: List[(String, TPTP.THF.Type)] = Nil): TPTP.THF.Formula = {
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
          conn match {
            case THF.Eq | THF.Neq => relativizedEq(conn)(left, right)
            case _ => THF.BinaryFormula(conn, convertedLeft, convertedRight)
          }

        case THF.ConnectiveTerm(_) => formula

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedVariableList = variableList map {
            case (str, tp) => (str, convertType(tp))
          }
          val convertedBody = convertFormula(body)(variableList.toList++variables)

          def relativizeVar(connective: THF.BinaryConnective)(v: (String, THF.Type), body: THF.Formula) = v match {
            case (str, tp) =>
              THF.BinaryFormula(connective, typePred(tp, THF.Variable(str)), body)
          }

          def relativizedBody(connective: THF.BinaryConnective) = variableList.foldRight(convertedBody)(relativizeVar(connective))
          quantifier match {
            case THF.! => THF.QuantifiedFormula(THF.!, convertedVariableList, relativizedBody(THF.Impl))
            case THF.? => THF.QuantifiedFormula(THF.?, convertedVariableList, relativizedBody(THF.&))
            case _ => THF.QuantifiedFormula(quantifier, convertedVariableList, convertedBody)
          }

        case v: THF.Variable => v
        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    private def convertPi(variableList: Seq[(String, THF.Type)], ret: THF.Type): THF.Type= {
      def convertFunType(v: (String, THF.Type), body: THF.Type): THF.Type = v match {
        case (_, tp) => FuncType(convertType(tp), convertType(body))
      }
      variableList.foldRight(ret)(convertFunType)
    }
    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, _) => THF.FunctionTerm(f, Seq.empty)
        case THF.QuantifiedFormula(THF.!>, variableList, body) => convertPi(variableList, convertType(body))
        case _ => typ
      }
    }

    @tailrec
    private def convertTypeFormula(formula: AnnotatedFormula): List[AnnotatedFormula] = {
      formula match {
        // Normalize nested pi-types to simplify the subsequent logic
        case TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl, THF.QuantifiedFormula(THF.!>, vl2, bdy))), an) =>
          convertTypeFormula(TPTP.THFAnnotated(n, "type", THF.Typing(s,THF.QuantifiedFormula(THF.!>, vl++vl2, bdy)), an))
        case TPTP.THFAnnotated(name, "type", TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedType = convertType(typ)
          var declType: THF.Type = univTp
          val base = atomicTerm(symbol)
          def typeRelDecls(variableList: Seq[(String, THF.Type)]) = {
            val declTp = convertPi(variableList, FuncType(base, FuncType(base, bool)))
            val tpRelDecl = TPTP.THFAnnotated(typeRelName(symbol), "type",
              TPTP.THF.Typing(typeRelName(symbol), declTp), annotations)

            val baseRelTp = THF.FunctionTerm(symbol, variableList map {v => THF.Variable(v._1)})
            def baseRel(x:String, y:String) = typeRel(baseRelTp, THF.Variable(x), THF.Variable(y))
            val symAx = THF.QuantifiedFormula(THF.!, Seq(("RX", base), ("RY", base)),
              THF.BinaryFormula(THF.Eq, baseRel("RX", "RY"), baseRel("RY", "RX")))
            val transAx = THF.QuantifiedFormula(THF.!, Seq(("RX", base), ("RY", base), ("RZ", base)),
              THF.BinaryFormula(THF.Impl, baseRel("RX", "RY"),
                THF.BinaryFormula(THF.Impl, baseRel("RY", "RZ"), baseRel("RX", "RZ"))))
            val reduceAx = THF.QuantifiedFormula(THF.!, Seq(("RX", base), ("RY", base)),
              THF.BinaryFormula(THF.Eq, THF.BinaryFormula(THF.&, THF.BinaryFormula(THF.Eq,
                THF.Variable("RX"), THF.Variable("RY")), baseRel("RX", "RX")), baseRel("RX", "RY")))
            def axiom(formulaBody: THF.Formula) = if (variableList.nonEmpty) {
              THF.Logical(THF.QuantifiedFormula(THF.!, variableList, formulaBody))
            } else {
              THF.Logical(formulaBody)
            }

            val tpRelSym = TPTP.THFAnnotated(typeRelSymName(symbol),
              "axiom", axiom(symAx), annotations)
            val tpRelTrans = TPTP.THFAnnotated(typeRelTransName(symbol),
              "axiom", axiom(transAx), annotations)
            val tpRelReduce = TPTP.THFAnnotated(typeRelReduceName(symbol),
              "axiom", axiom(reduceAx), annotations)
            List(tpRelDecl, tpRelSym, tpRelTrans, tpRelReduce)
          }
          val type_pred = typ match {
            // A generic type declaration
            case THF.QuantifiedFormula(THF.!>, variableList, ret) if ret == univTp =>
              typeRelDecls(variableList)
            // special case of a type declaration with no arguments
            case THF.FunctionTerm("$tType", Seq()) => typeRelDecls(Nil)
            // This is a term declaration
            case _ =>
              declType = convertedType
              constants ::= (symbol, typ)
              val tpPred = typePred(typ,base)
              List(TPTP.THFAnnotated(axName(symbol), "axiom", THF.Logical(tpPred), annotations))
          }
          val convertedTyping = TPTP.THF.Typing(symbol, declType)
          val convertedFormula = TPTP.THFAnnotated(name, "type", convertedTyping, annotations)
          convertedFormula::type_pred
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
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
    private def relativizedEq(conn: THF.BinaryConnective)(left: THF.Formula, right: THF.Formula)(implicit variables: List[(String, TPTP.THF.Type)] = Nil) : THF.Formula = {
      val convertedLeft: TPTP.THF.Formula = convertFormula(left)
      val convertedRight: TPTP.THF.Formula = convertFormula(right)
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
        case THF.Eq  => typeRel(eqType, convertedLeft, convertedRight)
        case THF.Neq => THF.UnaryFormula(THF.~, typeRel(eqType, convertedLeft, convertedRight))
        case _ => THF.BinaryFormula(conn, convertedLeft, convertedRight)
      }
    }
    /**
     * Generates the typing condition for the given type and term supposedly of that type
     * @param typ the type for which to generate the typing condition
     * @param tm the term for which to generate the typing condition
     * @return
     */
    private def typePred(typ: THF.Formula, tm: THF.Formula): THF.Formula = {
      typeRel(typ, tm, tm)
    }

    /**
     * Generates the typing condition, expands typing relations over Pi-types
     * @param typ the type of the typing relation
     * @param left the term on the left of the typing relation
     * @param right the term on the right of the typing relation
     * @return the typing relation for type typ applied to left and right
     */
    private def typeRel(typ: THF.Formula, left: THF.Formula, right: THF.Formula): THF.Formula = {
      def relAppl(tp: THF.FunctionTerm, left: THF.Formula, right: THF.Formula) = tp match {
        case THF.FunctionTerm(f, args) =>
          THF.FunctionTerm(typeRelName(f), args.map(convertFormula).appendedAll(Seq(left, right)))
      }
      // optimized version of typeRel in first-order
      def optimizedRelAppl(tp: THF.FunctionTerm, left: THF.Formula, right: THF.Formula) = {
        // we might translate relAppl via the reduceAx axiom rather than directly to a PER
        // however brief testing suggests that this doesn't really improve the performance of the overall prover system
        relAppl(tp, left, right)
      }

      def typeRelFuncType(x: String, tp: THF.Type, codomain: THF.Formula) = {
        val convertedTp = convertType(tp)
        val leftAppl = left match {
          case THF.FunctionTerm(s, args) => THF.FunctionTerm(s, args.:+(THF.Variable(x)))
          case _ => THF.BinaryFormula(THF.App, left, THF.Variable(x))
        }
        val rightAppl = right match {
          case THF.FunctionTerm(s, args) => THF.FunctionTerm(s, args.:+(THF.Variable(x)))
          case _ => THF.BinaryFormula(THF.App, right, THF.Variable(x))
        }
        val innerEq = codomain match {
          case f: FunctionTerm => optimizedRelAppl(f, leftAppl, rightAppl)
          case _ => typeRel(codomain, leftAppl, rightAppl)
        }

        THF.QuantifiedFormula(THF.!, Seq((x, convertedTp), (primedName(x), convertedTp)),
          THF.BinaryFormula(THF.Impl, typeRel(tp, TPTP.THF.Variable(x), TPTP.THF.Variable(primedName(x))),
            innerEq))
      }
      typ match {
        case DHOLEmbeddingUtils.bool => THF.BinaryFormula(THF.Eq, left, right)
        case f@THF.FunctionTerm(_, _) => optimizedRelAppl(f, left, right)
        case THF.BinaryFormula(THF.FunTyConstructor, tp, codomain)  =>
          val x = "x_"+tp.pretty
          typeRelFuncType(x, tp, codomain)
        case THF.QuantifiedFormula(THF.!>, vl, body) => vl.toList match {
          case (x,tp)::variableList =>
            val codomain = THF.QuantifiedFormula(THF.!>, variableList, body)
            typeRelFuncType(x, tp, codomain)
          case Nil => typeRel(body, left, right)
        }
        case _ => throw new EmbeddingException(s"Typing relation not defined on unsupported type '$name': '${typ.pretty}'")
      }
    }

    private def typeRelName(f:String): String = f+"_rel"
    private def typeRelSymName(f:String): String = typeRelName(f)+"_sym"
    private def typeRelTransName(f:String): String = typeRelName(f)+"_trans"
    private def typeRelReduceName(f:String): String = typeRelName(f)+"_reduce"
    private def axName(f:String): String = f+"_tp_ax"
    private def primedName(x: String) = x+"_prime"
  }
}

object DHOLEmbeddingUtils {
  private[embeddings] def atomicTerm(s:String): THF.Formula = THF.FunctionTerm(s, Seq.empty)
  private[embeddings] val bool = atomicTerm("$o")
  private[embeddings] val univTp = atomicTerm("$tType")
  private[embeddings] def FuncType(A: THF.Formula, B:THF.Formula) = THF.BinaryFormula(THF.FunTyConstructor, A, B)

  /** The application of function func to the arguments args */
  private[embeddings] def THFApply(func: THF.Formula, args: List[THF.Formula]): THF.Formula = {
    func match {
      case THF.FunctionTerm(f, fargs) => THF.FunctionTerm(f, fargs++args)
      case _ =>
        args match {
          case Nil => func
          case List(arg) => THF.BinaryFormula(THF.App, func, arg)
          case hd::tl => THF.BinaryFormula(THF.App, func, THFApply(hd, tl))
        }
    }
  }
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