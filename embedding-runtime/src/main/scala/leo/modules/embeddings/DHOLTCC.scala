package leo.modules.embeddings


import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, Annotations, THF}
import leo.datastructures.TPTP.THF.FunctionTerm

import scala.annotation.tailrec
import scala.math.Ordering.String

/**
 * @author Daniel Renalter, 2025
 */
object DHOLTCC extends EmbeddingN {
  import DHOLEmbeddingUtils._
  var constants : List[(String, TPTP.THF.Type)] = Nil
  var GLOBAL_VAR_CNT:Int = 0
  def getNewVarNr(): Int = {
    GLOBAL_VAR_CNT += 1
    GLOBAL_VAR_CNT
  }

  object DHOLEmbeddingParameter extends Enumeration { }
  /** The type of parameter options provided by the embedding instance. */
  override type OptionType = DHOLEmbeddingParameter.type

  /** The name of the embedding */
  override def name: String = "$$dholtc"

  /** The version number of the embedding instance implementation. */
  override def version: String = "0.1"

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

  override def applyN(problem: TPTP.Problem, embeddingOptions: Set[DHOLEmbeddingParameter.Value]): Seq[TPTP.Problem] = new DHOLTCImpl(problem).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class DHOLTCImpl(problem: TPTP.Problem) {
    def apply(): List[TPTP.Problem] = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val (_, (formulas:List[TPTP.THFAnnotated])) = splitInput(problemTHF.formulas)
      typeCheckConjecture(formulas.map(uniquifyVarNames))
    }

    private def typeRelName(f:String): String = f+"Star"
    private def typeRelSymName(f:String): String = typeRelName(f)+"_sym"
    private def typeRelTransName(f:String): String = typeRelName(f)+"_trans"
    private def typeRelReduceName(f:String): String = typeRelName(f)+"_reduce"
    private def axName(f:String): String = f+"_tp_ax"
    private def primedName(x: String) = x+"_prime"
    private def genPerType(a: THF.Type) = THF.BinaryFormula(THF.FunTyConstructor, a, (THF.BinaryFormula(THF.FunTyConstructor, a, bool)))
    private def isPerPred = THF.FunctionTerm("isPer", Seq())

    private def atomicTerm(s:String): THF.Formula = THF.FunctionTerm(s, Seq.empty)
    private val bool = atomicTerm("$o")
    private val univTp = atomicTerm("$tType")
    private def FuncType(A: THF.Formula, B:THF.Formula) = THF.BinaryFormula(THF.FunTyConstructor, A, B)

    private def collectVars(f: THF.Formula): List[THF.TypedVariable] = f match {
      case THF.QuantifiedFormula(_, variableList, body) => (variableList.toList)++collectVars(body)
      case THF.BinaryFormula(_, left, right) => collectVars(left) ++ collectVars(right)
      case THF.UnaryFormula(_, body) => collectVars(body)
      case _ => Nil
    }

    def typeCheckConjecture(formulas: List[TPTP.THFAnnotated]): List[TPTP.Problem] = {
      val (conjectureFormulas, contextFormulas) = formulas.partition(_.role == "conjecture")
      val (typeFormulas, nonTypeFormulas) = contextFormulas.partition(_.role == "type")
      if (conjectureFormulas.length != 1)
        throw new EmbeddingException("Incorrect number of conjectures")
      val conjecture = conjectureFormulas.head match{
        case TPTP.THFAnnotated(_, "conjecture", THF.Logical(f), _) => f
        case _ => throw new EmbeddingException("this should be imposisble")
      }

      val constants = typeFormulas map {case TPTP.THFAnnotated(_, _, THF.Typing(n, t), _) => (n, t)}
//      println("in typecheck conjecture") //DEBUG
      val obligations = checkType(List[(String, THF.Type)](), constants.toList, List[THF.Formula]())(conjecture, bool).filter(x => x.exists(y => y.role == "conjecture"))
      obligations.map(x => TPTP.Problem(problem.includes, contextFormulas.toList ++ x, Map.empty))
    }

    private def genObligationFormula(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)], context: List[THF.Formula])(a: THF.Type, b:THF.Type): List[TPTP.THFAnnotated] = {
      val conj:THF.Formula = THF.BinaryFormula(THF.Eq, a, b)
      val usedVars = (context++List(conj)).flatMap(y => (variables.filter(x => occurs(y, x._1)))).distinct
      var witnesses = usedVars
      var newConj = conj
      var newContext = context
      var newWitnesses = witnesses
      if (!usedVars.isEmpty) {
        witnesses = usedVars.map(x => (x._1.toLowerCase(), x._2))
        newConj = usedVars.foldLeft(conj)((acc, v) => variableReplace(acc, (v._1, THF.FunctionTerm(v._1.toLowerCase(), Seq()))))
        newContext = context.map(x => (usedVars.foldLeft(x)((acc, v) => variableReplace(acc, (v._1, THF.FunctionTerm(v._1.toLowerCase(), Seq()))))))
        newWitnesses = witnesses.map(x => (x._1, (usedVars.foldLeft(x._2)((acc, v) => variableReplace(acc, (v._1, THF.FunctionTerm(v._1.toLowerCase(), Seq())))))))
      }
      newConj match {
        case THF.BinaryFormula(THF.Eq, a, b) => if (a == b) return Nil
      }
      var newFormulas = newWitnesses.zipWithIndex map (x => TPTP.THFAnnotated("witness" + x._2, "type", THF.Typing(x._1._1, x._1._2), None))
      newFormulas ++= newContext.zipWithIndex map (x => TPTP.THFAnnotated("context" + x._2, "axiom", THF.Logical(x._1), None))
      newFormulas ++= List(TPTP.THFAnnotated("Type Checking Constraint", "conjecture", THF.Logical(newConj), None))
//      println(newFormulas)    //DEBUG
      return newFormulas
    }

    private def genObligation(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)], context: List[THF.Formula])(a: THF.Type, b:THF.Type): List[List[TPTP.THFAnnotated]] = (a, b) match {
      case (a, b) if (a == b) => Nil
      case (THF.QuantifiedFormula(THF.!>, ahead::avl, af), THF.QuantifiedFormula(THF.!>, bhead::bvl, bf)) =>
        genObligation(variables, constants, context)(ahead._2, bhead._2) ++
        genObligation(variables++List(ahead)++List(bhead), constants, context)(THF.QuantifiedFormula(THF.!>, avl, af), THF.QuantifiedFormula(THF.!>, bvl, bf))
      case (THF.QuantifiedFormula(THF.!>, Nil, af), THF.QuantifiedFormula(THF.!>, Nil, bf)) =>
        genObligation(variables, constants, context)(af, bf)
      case (THF.BinaryFormula(THF.FunTyConstructor, al, ar), THF.BinaryFormula(THF.FunTyConstructor, bl, br)) =>
        genObligation(variables, constants, context)(al, bl) ++
        genObligation(variables, constants, context)(ar, br)
      case (THF.BinaryFormula(THF.App, al, ar), THF.BinaryFormula(THF.App, bl, br)) =>
        val (abase@THF.FunctionTerm(an, _), aargs) = unApply(a)
        val (bbase@THF.FunctionTerm(bn, _), bargs) = unApply(b)
        if (abase == bbase) {
          if (aargs.length == bargs.length)
            aargs.lazyZip(bargs).map((x,y) => (genObligationFormula(variables, constants, context)(x, y)))
          else
            List(genObligationFormula(variables, constants, context)(a, b))
        } else {
          List(genObligationFormula(variables, constants, context)(a, b))
        }
      case (a, b) =>
        List(genObligationFormula(variables, constants, context)(a, b))
    }

    //Check simply typed skeleton
    private def checkType(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)], context: List[THF.Formula])(formula: THF.Formula, targetType: THF.Type): List[List[TPTP.THFAnnotated]] = {
      def getArgTypes(formula: THF.Formula): List[THF.Type] = formula match {
        case THF.BinaryFormula(THF.FunTyConstructor, a, b) => a :: getArgTypes(b)
        case THF.QuantifiedFormula(THF.!>, Nil, f) => getArgTypes(f)
        case THF.QuantifiedFormula(THF.!>, vl, f) =>
          vl.toList.head._2 :: getArgTypes(THF.QuantifiedFormula(THF.!>, vl.toList.tail, f))
        case _ => Nil
      }
      // DEBUG
      /*
      println("-----------------")
      println("using variables: ")
      variables map (x => println(" - " + x._1 + ":" + x._2.pretty))
      println("using constants: ")
      constants map (x => println(" - " + x._1 + ":" + x._2.pretty))
      println("using context: ")
      context map (x => println(" - " + x.pretty))
       println("checking if: " + formula.pretty + " is of type " + targetType.pretty)
       */
      formula match {
        case THF.UnaryFormula(_, f) => 
          if (targetType == bool)
            checkType(variables, constants,context)(f, bool)
          else
            throw new EmbeddingException("Error in typing the simple skeleton:"+f.pretty)
        case THF.QuantifiedFormula(q, vl, f) => 
          if (vl.isEmpty) {
            checkType(variables, constants, context)(f, targetType)
          } else {
            q match {
              case THF.! | THF.? =>
                if (targetType == bool)
                  checkType(variables++vl.toList, constants, context)(f, bool)
                else
                  throw new EmbeddingException("Error in typing the simple skeleton:"+f.pretty)
              case THF.!> =>
                if (targetType == univTp) {
                  if (vl.isEmpty)
                    checkType(variables, constants, context)(f, targetType)
                  else {
                    val curVar = vl.head
                    checkType(variables, constants, context)(curVar._2, targetType) ++
                    checkType(variables++List(curVar), constants, context)(THF.QuantifiedFormula(q, vl.tail, f), targetType)
                  }
                }
                else
                  throw new EmbeddingException("No type-hirarchy. " + formula.pretty + " must be of type " + univTp.pretty + " is of type " + targetType.pretty + ".")
              case THF.^ =>
                if (vl.isEmpty)                                                                                  //catch empty quantifier list due to processing
                  checkType(variables, constants, context)(f, targetType)
                else {
                  val curVar = vl.head
                  targetType match {
                    case THF.QuantifiedFormula(THF.!>, (curType@(n, curVar._2)) :: ivl, b) =>
                      checkType(variables++List(curVar)++List(curType), constants, context)(THF.QuantifiedFormula(q, vl.tail, f) , THF.QuantifiedFormula(THF.!>, ivl, b))
                    case THF.BinaryFormula(THF.FunTyConstructor, curVar._2, b) =>
                      checkType(variables++List(curVar), constants, context)(THF.QuantifiedFormula(q, vl.tail, f), b)
                    case b => throw new EmbeddingException("Error in typing the simple skeleton:"+f.pretty+ " needs to have a function type, but is of type " + b.pretty)
                  }
                }
              case _ =>
                throw new EmbeddingException("Unsupported quantifier:"+q)                                        //other quantifiers (SumTypeConst, ProdTypeConst, Choice, Selection) not supported
            }
          }
        case f@THF.BinaryFormula(c, l, r) =>
          c match {
            case THF.App =>                                                                                    
              val (base@THF.FunctionTerm(n, _), args) = unApply(f)
              val varsInContext = variables.filter(x => (x._1 == n))
              val constsInContext = constants.filter(x => (x._1 == n))
              val termsInContext = varsInContext ++ constsInContext
              if (termsInContext.length > 1)
                throw new EmbeddingException("Inconsistent variable/constant list: multiple entries for "+ n)
              val found = termsInContext.head
              val instanciatedBaseTypeArgs =
                found._2 match {
                  case THF.QuantifiedFormula(THF.!>, vl, f) =>
                    val replacements = (vl.map(_._1)).zip(args.take(vl.length))
                    val instanciatedBase = replacements.foldLeft(found._2)((acc, replace) => variableReplace(acc, replace))
                    getArgTypes(instanciatedBase)
                  case THF.BinaryFormula(THF.FunTyConstructor, l, r) =>
                    getArgTypes(found._2)
                  case t =>
                    throw new EmbeddingException("Unexpected type: " + t.pretty + " for term " + base.pretty)
                }
//              args map (x => println(x.pretty))
//              println(" for basetypeargs \n")
//              instanciatedBaseTypeArgs map (x => println(x.pretty))
              if (args.length == instanciatedBaseTypeArgs.length) {
                genObligation(variables, constants, context)(inferType(variables, constants)(f), targetType) ++
                (args.lazyZip(instanciatedBaseTypeArgs) flatMap ((x,y) => checkType(variables, constants, context)(x,y)))
              } else {
                throw new EmbeddingException("Mismatch in the number of arguments of function application.")
              }
            case THF.Eq =>
              if (targetType == bool) {
                val lSubs = (properInferType(variables, constants)(l))
                val lType = lSubs.find(_._1.name == "Alhpa").get 
//                println("after infer type left: ")
//                lSubs.map(x => println(x._1.pretty + ":" + x._2.pretty))
                val rSubs = (properInferType(variables, constants)(r))
                val rType = rSubs.find(_._1.name == "Alhpa").get
//                println("after infer type right: ")
//                rSubs.map(x => println(x._1.pretty + ":" + x._2.pretty))
                genObligation(variables, constants, context)(lType._2, rType._2) ++
                  checkType(variables, constants, context)(l, lType._2) ++
                  checkType(variables, constants, context)(r, rType._2)
              }
              else
                throw new EmbeddingException("Error in typing the simple skeleton: Equality "+f.pretty+" needs to be of type bool")
            case THF.Neq =>
              if (targetType == bool)
                checkType(variables, constants, context)(THF.BinaryFormula(THF.Eq, l, r), bool)                            // A != B -> not (A = B) -> if bool the typecheck is equal to negation
              else
                throw new EmbeddingException("Error in typing the simple skeleton:"+f.pretty)
            case THF.FunTyConstructor =>                                                                                   // non-dependent version of QuantifiedFormula(!>...
              if (targetType == univTp) {
                checkType(variables, constants, context)(l, univTp) ++
                checkType(variables, constants, context)(r, univTp)
              }
              else
                throw new EmbeddingException("No type-hirarchy. " + formula.pretty + " must be of type " + univTp.pretty + " is of type " + targetType.pretty + ".")
            case THF.Impl | THF.& | THF.~& =>
              if (targetType == bool) {
                val usedVars = variables.filter(x => occurs(l, x._1))
                val conj = l
                checkType(variables, constants, context)(l, targetType) ++ checkType(variables, constants, (conj::context))(r, targetType)
              }
              else
                throw new EmbeddingException("Error in typing the simple skeleton: Boolean "+f.pretty+" needs to be of type bool")
            case THF.<= =>
              if (targetType == bool)
                checkType(variables, constants, context)(THF.BinaryFormula(THF.Impl, r, l), targetType)
              else
                throw new EmbeddingException("Error in typing the simple skeleton: Boolean "+f.pretty+" needs to be of type bool")
            case THF.| | THF.~| =>
              if (targetType == bool) {
                val usedVars = variables.filter(x => occurs(l, x._1))
                val conj = l
                checkType(variables, constants, context)(l, targetType) ++ checkType(variables, constants, (THF.UnaryFormula(THF.~, conj))::context)(r, targetType)
              }
              else
                throw new EmbeddingException("Error in typing the simple skeleton: Boolean "+f.pretty+" needs to be of type bool")
            case c =>
              if (targetType == bool)
                checkType(variables, constants, context)(l, bool) ++ checkType(variables, constants, context)(r, bool)
              else                                                                                             //Product types, Sum types are not supported, and definitions can't appear in conjectures
                throw new EmbeddingException("Connective " + c.pretty + "not supported in typing.")
          }
        case THF.FunctionTerm("$o", Seq()) =>
          if (targetType == univTp)
            return Nil
          else
            throw new EmbeddingException("Bool cannot be of type " + targetType.pretty)
        case THF.FunctionTerm("$tType", Seq()) =>
          return Nil
        case THF.FunctionTerm(n, Seq()) =>
          val varsInContext = variables.filter(x => (x._1 == n))
          val constsInContext = constants.filter(x => (x._1 == n))
          val termsInContext = varsInContext ++ constsInContext
          if (termsInContext.length != 1)
            throw new EmbeddingException("Inconsistent variable/constant list: too few/multiple entries for "+ n)
          val found = termsInContext.head
          genObligation(variables, constants, context)(targetType, found._2)
        case THF.Variable(n) =>
//          println("typechecking " + n + " against " + targetType.pretty)
          val varsInContext = variables.filter(x => (x._1 == n))
          val constsInContext = constants.filter(x => (x._1 == n))
          val termsInContext = varsInContext ++ constsInContext
          if (termsInContext.length != 1)
            throw new EmbeddingException("Inconsistent variable/constant list: too few/multiple entries for "+ n)
          val found = termsInContext.head
          genObligation(variables, constants, context)(targetType, found._2)
        case _ =>
          throw new EmbeddingException("Unknown error while checking " + formula.pretty + " against type " + targetType.pretty)
      }
    }

    private def unApply(formula: THF.Formula): (THF.FunctionTerm, List[THF.Formula]) = {
      def auxUnApply(formula: THF.Formula, acc: List[THF.Formula]): (THF.FunctionTerm, List[THF.Formula]) = formula match {
        case THF.BinaryFormula(THF.App, l, r) => auxUnApply(l, r::acc)
        case f@THF.FunctionTerm(_,_) => (f, acc)
        case f@THF.Variable(n) => (THF.FunctionTerm(n, Seq()), acc)
        case f => throw new EmbeddingException("unApply: unexpected term found: "+f.pretty)
      }
      auxUnApply(formula, Nil)
    }

    private def properInferType(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)])(formula: THF.Formula): List[(THF.Variable, THF.Type)] = { 
      var varCnt = 0
      def getFreshTypeVar: THF.Type = { //the typos are features and prevent clashes with names in the problem file (:
        varCnt += 1
        THF.Variable("Alhpa"+(varCnt-1))
      }
      def getFreshVarName: String = {
        varCnt += 1
        "FreshIntorducedVarName"+(varCnt-1)
      }
      def properInferTypeAux(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)], arguments: List[THF.Formula])(f: THF.Formula, t: THF.Type): List[THF.BinaryFormula] = {
//        println("infering type of: " + f.pretty + "( " + f + " )")
        f match {
          case THF.FunctionTerm(n, _) =>
//            println("infering type of constant/variable " + n)
            val foundVal = (constants++variables).find(_._1 == n)
            if (foundVal != None){
              var ret = foundVal.get._2
              if (arguments != Nil)
                ret = arguments.foldLeft(foundVal.get._2)((acc, v) => applyFunction(variables, constants, Nil)(acc, v))
//              println(" and found: " + ret + ", assigned to " + t)
              List(THF.BinaryFormula(THF.Eq, uniquifyVarNamesAux(ret), t))
            }
            else
              throw new EmbeddingException("Failed to find variable or constant during type inference: " + f.pretty + " : " + t.pretty)
          case THF.BinaryFormula(THF.App, l, r) =>
            val rType = properInferType(variables, constants)(r).find(_._1.name == "Alhpa").get._2
//            println("rType = " + rType)
            if (rType == univTp) {
              properInferTypeAux(variables, constants, arguments++List(r))(l, t)
            } else {
              val freshVarName = getFreshVarName
              val freshTypeVar = getFreshTypeVar
              properInferTypeAux(variables, constants, arguments)(l, THF.QuantifiedFormula(THF.!>, List((freshVarName, freshTypeVar)), t)) ++ properInferTypeAux(variables, constants, arguments)(r, freshTypeVar)
            }
          case THF.BinaryFormula(THF.FunTyConstructor, l, r) =>
            throw new EmbeddingException("Function Type Constructor not allowed on term level.")
          case THF.BinaryFormula(c@THF.SumTyConstructor, _, _) =>
            throw new EmbeddingException("Unsupported operator in type inference: " + c.pretty)
          case THF.BinaryFormula(c@THF.ProductTyConstructor, _, _) =>
            throw new EmbeddingException("Unsupported operator in type inference: " + c.pretty)
          case THF.BinaryFormula(c@THF.==, _, _) =>
            throw new EmbeddingException("Unsupported operator in type inference: " + c.pretty)
          case THF.BinaryFormula(c@THF.:=, _, _) =>
            throw new EmbeddingException("Unsupported operator in type inference: " + c.pretty)
          case THF.BinaryFormula(c, l, r) =>
            List(THF.BinaryFormula(THF.Eq, t, bool))
          case THF.UnaryFormula(_, i) =>
            List(THF.BinaryFormula(THF.Eq, t, bool))
          case THF.QuantifiedFormula(THF.^, Nil, i) =>
            properInferTypeAux(variables, constants, arguments)(i, t)
          case THF.QuantifiedFormula(THF.^, v::vl, i) =>
            val freshTypeVar = getFreshTypeVar
            properInferTypeAux(variables++List(v), constants, arguments)(THF.QuantifiedFormula(THF.^, vl, i), freshTypeVar) ++
            List(THF.BinaryFormula(THF.Eq, t, THF.QuantifiedFormula(THF.!>, List(v), freshTypeVar)))
          case THF.QuantifiedFormula(q@THF.!>, _, _) =>
            throw new EmbeddingException("Unsupported quantified in type inference: " + q.pretty)
          case THF.QuantifiedFormula(q@THF.?*, _, _) =>
            throw new EmbeddingException("Unsupported quantified in type inference: " + q.pretty)
          case THF.QuantifiedFormula(q@THF.@+, _, _) =>
            throw new EmbeddingException("Unsupported quantified in type inference: " + q.pretty)
          case THF.QuantifiedFormula(q@THF.@-, _, _) =>
            throw new EmbeddingException("Unsupported quantified in type inference: " + q.pretty)
          case THF.QuantifiedFormula(q, vl, i) =>
            List(THF.BinaryFormula(THF.Eq, t, bool))
          case THF.Variable(n) =>
            properInferTypeAux(variables, constants, arguments)(THF.FunctionTerm(n, Seq()), t)
        }
      }
      solveUnificationProblem(properInferTypeAux(variables, constants, Nil)(formula, THF.Variable("Alhpa")), List[(THF.Variable, THF.Type)]())
    }

    private def applyFunction(variables: List[(String, THF.Type)], constants: List[(String, THF.Type)], context: List[THF.Formula])(formula: THF.Formula, argument: THF.Formula) = formula match {
      case THF.QuantifiedFormula(THF.!>, v+:Nil, f) =>
        if(checkType(variables, constants, context)(argument, v._2) == Nil) //pretty inefficient, maybe reconsider
          variableReplace(f, (v._1, argument))
        else
          throw new EmbeddingException("Can't apply argument " + argument.pretty + " to function " + formula)
      case THF.QuantifiedFormula(THF.!>, v+:vl, f) =>
        if(checkType(variables, constants, context)(argument, v._2) == Nil) //pretty inefficient, maybe reconsider
          THF.QuantifiedFormula(THF.!>, vl, variableReplace(f, (v._1, argument)))
        else
          throw new EmbeddingException("Can't apply argument " + argument.pretty + " to function " + formula)
      case THF.BinaryFormula(THF.FunTyConstructor, l, r) =>
        if(checkType(variables, constants, context)(argument, l) == Nil)
          r
        else
          throw new EmbeddingException("Can't apply argument " + argument.pretty + " to function " + formula)
      case _ =>
        throw new EmbeddingException("Can't apply argument " + argument.pretty + " to function " + formula)
    }

    private def solveUnificationProblem(equations: List[THF.Formula], substitutions: List[(THF.Variable, THF.Type)]): List[(THF.Variable, THF.Type)] = { //formula is either function term or variable
// DEBUG
//      println("=============================")
//      equations map (x => println(x.pretty))
//      println("=============================")
      if(!equations.isEmpty) {
//        println("unifying " + equations.head)
        equations.head match {
          case THF.BinaryFormula(_, x, y) if (x == y) =>
            solveUnificationProblem(equations.tail, substitutions)
          case THF.BinaryFormula(_, l@THF.BinaryFormula(THF.App, _, _), r@THF.BinaryFormula(THF.App, _, _)) =>
            var (lb, largs) = unApply(l)
            var (rb, rargs) = unApply(r)
            if (lb == rb)
              solveUnificationProblem(equations.tail ++
                (largs.lazyZip(rargs) map ((x, y) => THF.BinaryFormula(THF.Eq, x, y))), substitutions)
            else
              throw new EmbeddingException("Function missmatch in unification: " + l.pretty + " and " + r.pretty)
          case THF.BinaryFormula(_, THF.QuantifiedFormula(THF.!>, lv+:lvl, lf), THF.QuantifiedFormula(THF.!>, rv+:rvl, rf)) =>
            solveUnificationProblem(equations.tail ++ List(THF.BinaryFormula(THF.Eq, lv._2, rv._2))
              ++ List(THF.BinaryFormula(THF.Eq, THF.QuantifiedFormula(THF.!>, lvl, lf),
                THF.QuantifiedFormula(THF.!>, rvl, rf))), substitutions)
          case THF.BinaryFormula(_, THF.QuantifiedFormula(THF.!>, lv+:lvl, lf), THF.BinaryFormula(THF.FunTyConstructor, rl, rr)) =>
            solveUnificationProblem(equations.tail ++ List(THF.BinaryFormula(THF.Eq, lv._2, rl))
              ++ List(THF.BinaryFormula(THF.Eq, THF.QuantifiedFormula(THF.!>, lvl, lf), rr)), substitutions)
          case THF.BinaryFormula(_, THF.BinaryFormula(THF.FunTyConstructor, ll, lr), THF.QuantifiedFormula(THF.!>, rv+:rvl, rf)) =>
            solveUnificationProblem(equations.tail ++ List(THF.BinaryFormula(THF.Eq, ll, rv._2))
              ++ List(THF.BinaryFormula(THF.Eq, lr, THF.QuantifiedFormula(THF.!>, rvl, rf))), substitutions)
          case THF.BinaryFormula(_, THF.QuantifiedFormula(THF.!>, Nil, lf), r) =>
            solveUnificationProblem(equations.tail ++ List(THF.BinaryFormula(THF.Eq, lf, r)), substitutions)
          case THF.BinaryFormula(_, l, THF.QuantifiedFormula(THF.!>, Nil, rf)) =>
            solveUnificationProblem(equations.tail ++ List(THF.BinaryFormula(THF.Eq, l, rf)), substitutions)
          case THF.BinaryFormula(_, ol@THF.Variable(l), or@THF.Variable(r)) =>
            val lNr = l.tail.toIntOption
            val rNr = r.tail.toIntOption
            val lgr = if (lNr != None && rNr != None) lNr.get > rNr.get else Ordering.String.gt(l, r)
            val rgl = if (lNr != None && rNr != None) rNr.get > lNr.get else Ordering.String.gt(r, l)
            if (!occurs(or, l) && lgr) {
              return solveUnificationProblem(equations.tail map (x => variableReplace(x, (l, or))), (ol, or) :: (substitutions.map (x => (x._1, variableReplace(x._2, (l, or))))))
            } else if (!occurs(ol, r) && rgl) {
              return solveUnificationProblem(equations.tail map (x => variableReplace(x, (r, ol))), (or, ol) :: (substitutions.map (x => (x._1, variableReplace(x._2, (r, ol))))))
            } else {
              return solveUnificationProblem(equations.tail ++ List(equations.head), substitutions)
            }
          case THF.BinaryFormula(_, l@THF.Variable(n), r) =>
            if (!occurs(r, n))
              solveUnificationProblem(equations.tail map (x => variableReplace(x, (n, r))), (l, r) :: (substitutions.map (x => (x._1, variableReplace(x._2, (n, r))))))
            else
              solveUnificationProblem(equations.tail ++ List(equations.head), substitutions)
          case THF.BinaryFormula(_, l, r@(THF.Variable(n))) =>
            if (!occurs(l, n)) {
              solveUnificationProblem(equations.tail map (x => variableReplace(x, (n, l))), (r, l) :: (substitutions.map (x => (x._1, variableReplace(x._2, (n, l))))))
            } else {
              solveUnificationProblem(equations.tail ++ List(equations.head), substitutions)
            }
          case x =>
            throw new EmbeddingException("Non-Equality handed to unification problem: " + x)
        }
      } else {
        return substitutions
      }
    }

    private def occurs(formula: THF.Formula, toFind: String): Boolean = formula match {
      case THF.UnaryFormula(_, f) =>
        occurs(f, toFind)
      case THF.BinaryFormula(_, l, r) =>
        occurs(l, toFind) || occurs(r, toFind)
      case THF.QuantifiedFormula(_, _, f) =>
        occurs(f, toFind)
      case f@THF.FunctionTerm(n, _) =>
        if (n == toFind)
          true
        else
          false
      case f@THF.Variable(n) =>
        if (n == toFind)
          true
        else
          false
      case _ =>
        throw new EmbeddingException("Unsupported formula in Occurs check: " + formula.pretty)
    }


    private def functionTermReplace(formula: THF.Formula, replace: (String, THF.Formula)): THF.Formula = {
      def functionTermReplaceVarList(list: List[THF.TypedVariable], replace: (String, THF.Formula)): List[THF.TypedVariable] = list match {
        case h::t =>
          (h._1, functionTermReplace(h._2, replace))::functionTermReplaceVarList(t, replace)
        case Nil => Nil
      }
      formula match {
        case THF.UnaryFormula(c, f) =>
          THF.UnaryFormula(c, functionTermReplace(f, replace))
        case THF.BinaryFormula(c, l, r) =>
          THF.BinaryFormula(c, functionTermReplace(l, replace), functionTermReplace(r, replace))
        case THF.QuantifiedFormula(q, vl, f) =>
          THF.QuantifiedFormula(q, functionTermReplaceVarList(vl.toList, replace), functionTermReplace(f, replace))
        case f@THF.FunctionTerm(n, _) =>
          if (n == replace._1) {
            replace._2
            }
          else
            f
        case f@THF.Variable(n) =>
          f
        case _ =>
          throw new EmbeddingException("Unsupported formula to replace in: " + formula)
      }
    }

    private def variableReplace(formula: THF.Formula, replace: (String, THF.Formula)): THF.Formula = {
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
        case f@THF.FunctionTerm(_, _) =>
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
      * Infer the type of the given term from the types of the constants and variables in scope
      * @param formula the term whoose type to infer
      * @param variables the variables in the scope of the term
      * @param constants the constants
      * @return
      */
    private def inferType(variables: List[(String, TPTP.THF.Type)], constants: List[(String, TPTP.THF.Type)])(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
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
    private def uniquifyVarNamesAux(formula: THF.Formula): THF.Formula = formula match {
        case THF.UnaryFormula(c, f) =>
          THF.UnaryFormula(c, uniquifyVarNamesAux(f))
        case THF.BinaryFormula(c, l, r) =>
          THF.BinaryFormula(c, uniquifyVarNamesAux(l), uniquifyVarNamesAux(r))
        case THF.QuantifiedFormula(q, vl, f) =>
          def aux(acc: THF.Formula, v: THF.TypedVariable):THF.QuantifiedFormula = acc match{
            case THF.QuantifiedFormula(q, vli, fi) =>
              val newV = "A"+getNewVarNr()
              val modifiedF = variableReplace(fi, (v._1, THF.Variable(newV)))
              val modifiedVl = vli.map(x => (x._1, variableReplace(uniquifyVarNamesAux(x._2), (v._1, THF.Variable(newV)))))
              THF.QuantifiedFormula(q, modifiedVl.tail ++ List((newV, modifiedVl.head._2)), modifiedF)
            case _ => throw new EmbeddingException("huh? " + acc.pretty)
          }
          val modifiedF = THF.QuantifiedFormula(q, vl, uniquifyVarNamesAux(f))
          vl.foldLeft(modifiedF)((acc, v) => aux(acc, v))
        case f@THF.FunctionTerm(_, _) =>
          f
        case f@THF.Variable(_) =>
          f
        case _ =>
          throw new EmbeddingException("Unsupported Formula Type: " + formula.pretty)
      }

    private def uniquifyVarNames(annotatedFormula: TPTP.THFAnnotated): TPTP.THFAnnotated = {
      annotatedFormula match {
        case TPTP.THFAnnotated(n, r, THF.Logical(f), a) =>
          TPTP.THFAnnotated(n, r, THF.Logical(uniquifyVarNamesAux(f)), a)
        case TPTP.THFAnnotated(n, r, THF.Typing(in, f), a) =>
          TPTP.THFAnnotated(n, r, THF.Typing(in, uniquifyVarNamesAux(f)), a)
        case _ =>
          throw new EmbeddingException("Sequent Formulas are not supported.")
      }
    }
  }
}
