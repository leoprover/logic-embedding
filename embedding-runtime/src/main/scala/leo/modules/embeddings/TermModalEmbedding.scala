package leo.modules.embeddings

import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, TFFAnnotated, THFAnnotated, TFF, THF}
import leo.modules.input.TPTPParser.annotatedTHF

import scala.annotation.unused

object TermModalEmbedding extends Embedding {

  object TermModalEmbeddingOption extends Enumeration {
    // Hidden on purpose, to allow distinction between the object itself and its values.
    //    type TermModalEmbeddingOption = Value
    @unused
    final val MONOMORPHIC, POLYMORPHIC = Value
  }

  override type OptionType = TermModalEmbeddingOption.type
  override final def embeddingParameter: TermModalEmbeddingOption.type = TermModalEmbeddingOption
  override final val name: String = "$$termmodal"
  override final val version: String = "1.0"

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated = {
    annotatedTHF(s"thf(logic_spec, logic, $name).")
  }

  override final def apply(problem: TPTP.Problem,
                           embeddingOptions: Set[TermModalEmbeddingOption.Value]): TPTP.Problem =
    new TermModalEmbeddingImpl(problem, embeddingOptions).apply()

  override final def apply(formulas: Seq[TPTP.AnnotatedFormula],
                           embeddingOptions: Set[TermModalEmbeddingOption.Value]): Seq[TPTP.AnnotatedFormula] =
    apply(TPTP.Problem(Seq.empty, formulas, Map.empty), embeddingOptions).formulas

  private[this] final class TermModalEmbeddingImpl(problem: TPTP.Problem, embeddingOptions: Set[TermModalEmbeddingOption.Value]) {
    import TermModalEmbeddingOption._
    import collection.mutable

    private val polymorphic: Boolean = embeddingOptions.contains(POLYMORPHIC) // default monomorphic
    private var frameConditions: Map[THF.Type, Seq[FrameCondition]] = Map.empty
    // For warnings that should go inside the output file
    private[this] val warnings: mutable.Buffer[String] = mutable.Buffer.empty

    private[this] var localFormulaExists = false
    private[this] var globalFormulaExists = false

    private[this] def createState(spec: TFFAnnotated): Unit = {
      spec.formula match {
        case TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(`name`, Seq()), TFF.Tuple(spec0))) =>
          spec0.foreach {
            case TFF.FormulaTerm(TFF.MetaIdentity(TFF.AtomicTerm("$$logic", Seq()), TFF.AtomicTerm(logicName, Seq()))) =>
              val logic = logicName match {
                case "$$logic_K" => K
                case "$$logic_D" => D
                case "$$logic_T" => T
                case "$$logic_K4" => K4
                case "$$logic_D4" => D4
                case "$$logic_S4" => S4
                case "$$logic_S5" => S5
                case s => throw new EmbeddingException(s"Unknown value '$s' for parameter '$$$$logic'.")
              }
              frameConditions = Map.empty.withDefaultValue(logicToConditions(logic))
            case s => throw new EmbeddingException(s"Unknown logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

    @inline private[this] def worldTypeName: String = "mworld"
    @inline private[this] def mglobal: THF.Formula = str2Fun("mglobal")
    @inline private[this] def mlocal: THF.Formula = str2Fun("mlocal")

    private[this] val quantifierTypes: mutable.Set[THF.Type] = mutable.Set.empty
    @inline private[this] def quantifierType(typ: THF.Type): Unit = {
      quantifierTypes += typ
    }
    private[this] val modalOperators: mutable.Set[THF.Type] = mutable.Set.empty
    @inline private[this] def mbox(term: THF.Formula, typ: THF.Type): THF.Formula = {
      if (polymorphic) {
        THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, str2Fun("mbox"), typ), term)
      } else {
        modalOperators += typ
        THF.BinaryFormula(THF.App, str2Fun(s"mbox_${serializeType(typ)}"), term)
      }
    }
    @inline private[this] def mdia(term: THF.Formula, typ: THF.Type): THF.Formula = {
      if (polymorphic) {
        THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, str2Fun("mdia"), typ), term)
      } else {
        modalOperators += typ
        THF.BinaryFormula(THF.App, str2Fun(s"mdia_${serializeType(typ)}"), term)
      }
    }
    private[this] val functionGoalTypes: mutable.Map[String, TFF.Type] = mutable.Map.empty
    private[this] def getGoalTypeOfType(ty: TFF.Type): TFF.Type = ty match {
      case TFF.AtomicType(_, _) => ty
      case TFF.MappingType(_, right) => right
      case _ => throw new EmbeddingException(s"Unexpected error in getGoalTypeOfType(ty = ${ty.pretty}).")
    }
    private[this] def getGoalTypeOfTerm(term: TFF.Term, boundVars: Map[String, TFF.Type]): TFF.Type = term match {
      case TFF.AtomicTerm(f, _) => functionGoalTypes(f)
      case TFF.Variable(name) => boundVars.get(name) match {
        case Some(ty) => ty
        case None => throw new EmbeddingException(s"Unbound variable in argument '${term.pretty}' to modal operator.")
      }
      case TFF.DistinctObject(name) => TFF.AtomicType("$i", Seq.empty)
      case TFF.NumberTerm(value) => value match {
        case TPTP.Integer(_) => TFF.AtomicType("$int", Seq.empty)
        case TPTP.Rational(_, _) => TFF.AtomicType("$rat", Seq.empty)
        case TPTP.Real(_, _, _) => TFF.AtomicType("$real", Seq.empty)
      }
      case TFF.FormulaTerm(_) => TFF.AtomicType("$o", Seq.empty)
      case TFF.Tuple(elements) => TFF.TupleType(elements.map(getGoalTypeOfTerm(_, boundVars)))
    }

    def apply(): TPTP.Problem = {
      val formulas = problem.formulas
      val (spec, sortFormulas, typeFormulas, definitionFormulas, otherFormulas) = splitTFFInputByDifferentKindOfFormulas(formulas)
      createState(spec)
//      if (frameConditions.isEmpty) throw new EmbeddingException("Unexpected error while reading logic specification.")

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

    private def convertTypeFormula(input: TFFAnnotated): THFAnnotated = input.formula match {
      case TFF.Typing(atom, typ) =>
        functionGoalTypes += (atom -> getGoalTypeOfType(typ))
        val convertedType = convertType(typ)
        THFAnnotated(input.name, input.role, THF.Typing(atom, convertedType), input.annotations)
      case _ => throw new EmbeddingException(s"Malformed type definition in formula '${input.name}', aborting.")
    }

    private def convertType(typ: TFF.Type): THF.Type = typ match {
      case TFF.AtomicType("$o", Seq()) =>
        THF.BinaryFormula(THF.FunTyConstructor, THF.FunctionTerm(worldTypeName, Seq.empty), THF.FunctionTerm("$o", Seq.empty))
      case TFF.AtomicType(name, Seq()) => THF.FunctionTerm(name, Seq.empty)
      case TFF.MappingType(left, right) =>
        val convertedLefts = left.map(convertType)
        val convertedRight = convertType(right)
        convertedLefts.foldRight(convertedRight){ case (l,r) => THF.BinaryFormula(THF.FunTyConstructor, l, r) }
      case _ => throw new EmbeddingException(s"TFX type '${typ.pretty}' not supported by the embedding.")
    }

    def convertDefinitionFormula(formula: TFFAnnotated): THFAnnotated = convertAnnotatedFormula(formula)

    def convertAnnotatedFormula(input: TFFAnnotated): THFAnnotated = {
      import leo.modules.tptputils._
      input.formula match {
        case TFF.Logical(formula) =>
          val convertedFormula0 = convertFormula(formula)
          val convertedFormula = input.role match {
            case "hypothesis" | "conjecture" => // assumed to be local
              localFormulaExists = true
              THF.BinaryFormula(THF.App, mlocal, convertedFormula0)
            case _ if isSimpleRole(input.role) => // everything else is assumed to be global
              globalFormulaExists = true
              THF.BinaryFormula(THF.App, mglobal, convertedFormula0)
            case _ => // role with subroles, check whether a subrole specified $local or $global explicitly
              getSubrole(input.role).get match {
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
          val updatedRole = toSimpleRole(input.role) match {
            case "hypothesis" => "axiom"
            case r => r
          }
          THFAnnotated(input.name, updatedRole, THF.Logical(convertedFormula), input.annotations)
        case _ => throw new EmbeddingException(s"Malformed annotated formula '${input.pretty}'.")
      }
    }

    private def convertFormula(formula: TFF.Formula): THF.Formula = convertFormula(formula, Map.empty)
    private def convertFormula(formula: TFF.Formula, boundVars: Map[String, TFF.Type]): THF.Formula = {
      formula match {
        case TFF.AtomicFormula(f, args) =>
          val simpleResult = THF.FunctionTerm(f, args.map(convertTerm))
          if (tptpDefinedPredicateSymbols.contains(f)) {
            THF.QuantifiedFormula(THF.^, Seq(("W", THF.FunctionTerm(worldTypeName, Seq.empty))), simpleResult)
          } else simpleResult

        case TFF.UnaryFormula(connective, body) =>
          val convertedBody = convertFormula(body, boundVars)
          val convertedConnective = convertConnective(connective, boundVars)
          THF.BinaryFormula(THF.App, convertedConnective, convertedBody)

        case TFF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertFormula(left, boundVars)
          val convertedRight = convertFormula(right, boundVars)
          val convertedConnective = convertConnective(connective, boundVars)
          THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, convertedConnective, convertedLeft), convertedRight)

        case TFF.NonclassicalPolyaryFormula(connective, args) =>
          val convertedArgs = args.map(convertFormula(_, boundVars))
          val convertedConnective = convertConnective(connective, boundVars)
          convertedArgs.foldLeft(convertedConnective){case (l,r) => THF.BinaryFormula(THF.App, l, r) }

        case TFF.QuantifiedFormula(quantifier, variableList, body) =>
          @inline val iType: TFF.Type = TFF.AtomicType("$i", Seq.empty)
          val canonicalVariableList = variableList.map {case (name, maybeTy) => (name, maybeTy.fold(iType)(identity))}
          val convertedBody = convertFormula(body, boundVars.concat(canonicalVariableList))
          canonicalVariableList.foldRight(convertedBody) { case (vari,matrix) =>
            val convertedType = convertType(vari._2)
            val convertedQuantifier = convertQuantifier(quantifier, convertedType)
            val abstraction = THF.QuantifiedFormula(THF.^, Seq((vari._1, convertedType)), matrix)
            THF.BinaryFormula(THF.App, convertedQuantifier, abstraction)
          }

        case TFF.Equality(left, right) =>
          val convertedLeft: THF.Formula = convertTerm(left)
          val convertedRight: THF.Formula = convertTerm(right)
          val body = THF.BinaryFormula(THF.Eq, convertedLeft, convertedRight)
          THF.QuantifiedFormula(THF.^, Seq(("W", THF.FunctionTerm(worldTypeName, Seq.empty))), body)

        case TFF.Inequality(left, right) =>
          val convertedLeft: THF.Formula = convertTerm(left)
          val convertedRight: THF.Formula = convertTerm(right)
          val body = THF.BinaryFormula(THF.Neq, convertedLeft, convertedRight)
          THF.QuantifiedFormula(THF.^, Seq(("W", THF.FunctionTerm(worldTypeName, Seq.empty))), body)

        case _ => throw new EmbeddingException("TXF operators not supported by the embedding.")
      }
    }

    private def convertTerm(term: TFF.Term): THF.Formula = term match {
      case TFF.AtomicTerm(f, args) => THF.FunctionTerm(f, args.map(convertTerm))
      case TFF.Variable(name) => THF.Variable(name)
      case TFF.DistinctObject(name) => THF.DistinctObject(name)
      case TFF.NumberTerm(value) => THF.NumberTerm(value)
      case TFF.Tuple(elements) => THF.Tuple(elements.map(convertTerm))
      case TFF.FormulaTerm(formula) => convertFormula(formula)
    }

    private def convertQuantifier(quantifier: TFF.Quantifier, convertedType: TPTP.THF.Type): THF.Formula = quantifier match {
      case TFF.! =>
        quantifierType(convertedType)
        if (polymorphic) {
          val forall = THF.FunctionTerm("mforall", Seq.empty)
          THF.BinaryFormula(THF.App, forall, convertedType)
        } else {
          THF.FunctionTerm(s"mforall_${serializeType(convertedType)}", Seq.empty)
        }
      case TFF.? =>
        quantifierType(convertedType)
        if (polymorphic) {
          val exists = THF.FunctionTerm("mexists", Seq.empty)
          THF.BinaryFormula(THF.App, exists, convertedType)
        } else {
          THF.FunctionTerm(s"mexists_${serializeType(convertedType)}", Seq.empty)
        }
    }

    private[this] lazy val inlineMifDef: THF.Formula =
      leo.modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mimplies @ B @ A)")
    private[this] lazy val inlineMniffDef: THF.Formula =
      leo.modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mequiv @ A @ B))")
    private[this] lazy val inlineMnorDef: THF.Formula =
      leo.modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mor @ A @ B))")
    private[this] lazy val inlineMnandDef: THF.Formula =
      leo.modules.input.TPTPParser.thf(s"^[A: $worldTypeName > $$o, B: $worldTypeName > $$o]: (mnot @ (mand @ A @ B))")

    private[this] def convertConnective(connective: TFF.Connective, boundVars: Map[String, TFF.Type]): THF.Formula = {
      connective match {
        // Classical cases
        case TFF.~ => str2Fun("mnot")
        case TFF.<=> => str2Fun("mequiv")
        case TFF.Impl => str2Fun("mimplies")
        case TFF.| => str2Fun("mor")
        case TFF.& => str2Fun("mand")
        // other connectives of TPTP are encoded in terms of the above
        case TFF.<= => inlineMifDef
        case TFF.<~> => inlineMniffDef
        case TFF.~| => inlineMnorDef
        case TFF.~& => inlineMnandDef
        /// Non-classical case
        case TFF.NonclassicalLongOperator(name, Seq(Right((TFF.AtomicTerm("term", Seq()),term)))) =>
          name match {
            case "$box" =>
              val argType = getGoalTypeOfTerm(term, boundVars)
              mbox(convertTerm(term), convertType(argType))
            case "$dia" =>
              val argType = getGoalTypeOfTerm(term, boundVars)
              mdia(convertTerm(term), convertType(argType))
            case _ => throw new EmbeddingException(s"Unknown connective name '$name'.")
          }
        case _ => throw new EmbeddingException(s"Unsupported connective: '${connective.pretty}'")
      }
    }

    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty
      /////////////////////////////////////////////////////////////
      // First: Introduce world type
      result.append(worldTypeTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Introduce mrel (as relation or as collection of relations)
      if (polymorphic) result.append(polyAccessibilityRelationTPTPDef())
      else modalOperators.foreach{ ty => result.append(monoAccessibilityRelationTPTPDef(ty)) }
      /////////////////////////////////////////////////////////////
      // Then: Give mrel properties
      val table = if (polymorphic) polyAxiomTable else monoAxiomTable
      modalOperators.foreach{ ty => result.appendAll(frameConditions(ty).flatMap(cond => table(cond).map(_.apply(ty))))}
      /////////////////////////////////////////////////////////////
      // Then: Define mglobal/mlocal
      if (localFormulaExists) result.appendAll(mlocalTPTPDef())
      if (globalFormulaExists) result.appendAll(mglobalTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define connectives
      result.appendAll(connectivesTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define modal operators
      if (polymorphic) result.appendAll(polyModalOperatorsTPTPDef())
      else modalOperators.foreach { ty => result.appendAll(monoModalOperatorsTPTPDef(ty)) }
      /////////////////////////////////////////////////////////////
      // Then: Define exist-in-world-predicates and quantifiers
      if (polymorphic) {
        if (quantifierTypes.nonEmpty) {
          result.appendAll(polyExistsInWorldTPTPDef()) // define poly eiw
          result.appendAll(polyQuantifierTPTPDef())
        }
      } else {
        quantifierTypes foreach { ty =>
          result.appendAll(monoExistsInWorldTPTPDef(ty)) // define eiw with standard axioms
          result.appendAll(monoQuantifierTPTPDef(ty))
        }
      }
      /////////////////////////////////////////////////////////////
      // Return all
      result.toSeq
    }

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTHF(s"thf($worldTypeName, type, $worldTypeName: $$tType).")
    }

    private[this] def monoAccessibilityRelationTPTPDef(ty: THF.Type): TPTP.AnnotatedFormula = {
      annotatedTHF(s"thf(mrel_${serializeType(ty)}_type, type, mrel_${serializeType(ty)}: ${ty.pretty} > $worldTypeName > $worldTypeName > $$o).")
    }

    private[this] def polyAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      annotatedTHF(s"thf(mrel_type, type, mrel: !>[T:$$tType]: (T > $worldTypeName > $worldTypeName > $$o)).")
    }

    private[this] def mglobalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mglobal_type, type, mglobal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mglobal_def, definition, mglobal = (^ [Phi: $worldTypeName > $$o]: ![W: $worldTypeName]: (Phi @ W)) ).")
      )
    }

    private[this] def mlocalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mactual_type, type, mactual: $worldTypeName)."),
        annotatedTHF(s"thf(mlocal_type, type, mlocal: ($worldTypeName > $$o) > $$o)."),
        annotatedTHF(s"thf(mlocal_def, definition, mlocal = (^ [Phi: $worldTypeName > $$o]: (Phi @ mactual)) ).")
      )
    }

    private[this] def connectivesTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
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

    private[this] def monoModalOperatorsTPTPDef(ty: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mbox_${serializeType(ty)}_type, type, mbox_${serializeType(ty)}: ${ty.pretty}>($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mbox_${serializeType(ty)}_def, definition, ( mbox_${serializeType(ty)} = (^ [T:${ty.pretty},Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel_${serializeType(ty)} @ T @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_${serializeType(ty)}_type, type, mdia_${serializeType(ty)}: ${ty.pretty}>($worldTypeName>$$o)>$worldTypeName>$$o )."),
        annotatedTHF(s"thf(mdia_${serializeType(ty)}_def, definition, ( mdia_${serializeType(ty)} = (^ [T:${ty.pretty},Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel_${serializeType(ty)} @ T @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def polyModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mbox_type, type, mbox: !>[T: $$tType]: (T>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [T:$$tType, Term:T, Phi:$worldTypeName>$$o, W:$worldTypeName]: ![V:$worldTypeName]: ( (mrel @ T @ Term @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(mdia_type, type, mdia: !>[T: $$tType]: (T>($worldTypeName>$$o)>$worldTypeName>$$o) )."),
        annotatedTHF(s"thf(mdia_def, definition, ( mdia = (^ [T:$$tType, Term:T, Phi:$worldTypeName>$$o, W:$worldTypeName]: ?[V:$worldTypeName]: ( (mrel @ T @ Term @ W @ V) & (Phi @ V) )))).")
      )
    }

    private[this] def monoExistsInWorldTPTPDef(ty: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(eiw_${serializeType(ty)}_type,type, eiw_${serializeType(ty)}: ${ty.pretty} > $worldTypeName > $$o )."),
        annotatedTHF(s"thf(eiw_${serializeType(ty)}_cumul, axiom, ![W:$worldTypeName, V:$worldTypeName, E:${ty.pretty}]: ((mrel_${serializeType(ty)} @ E @ W @ V) => ( ![X:${ty.pretty}]: ((eiw_${serializeType(ty)} @ X @ W) => (eiw_${serializeType(ty)} @ X @ V)) ) )  ).")
      )
    }

    private[this] def polyExistsInWorldTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(eiw_type, type, eiw: !>[T:$$tType]: (T > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(eiw_cumul, axiom, ![T: $$tType, W:$worldTypeName, V:$worldTypeName, E:T]: ((mrel @ T @ E @ W @ V) => ( ![X:T]: ((eiw @ T @ X @ W) => (eiw @ T @ X @ V)) ) )  ).")
      )
    }

    private[this] def monoQuantifierTPTPDef(typ: THF.Type): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_type, type, mforall_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mforall_${serializeType(typ)}_def, definition, mforall_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ! [X:${typ.pretty}]: ((eiw_${serializeType(typ)} @ X @ W) => (A @ X @ W))))."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_type, type, mexists_${serializeType(typ)}: (${typ.pretty} > $worldTypeName > $$o) > $worldTypeName > $$o)."),
        annotatedTHF(s"thf(mexists_${serializeType(typ)}_def, definition, mexists_${serializeType(typ)} = ( ^ [A:${typ.pretty}>$worldTypeName>$$o, W:$worldTypeName]: ? [X:${typ.pretty}]: ((eiw_${serializeType(typ)} @ X @ W) & (A @ X @ W)))).")
      )
    }

    private[this] def polyQuantifierTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      Seq(
        annotatedTHF(s"thf(mforall_type, type, mforall: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mforall_def, definition, mforall = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ! [X:T]: ((eiw @ T @ X @ W) => (A @ X @ W))))."),
        annotatedTHF(s"thf(mexists_type, type, mexists: !>[T:$$tType]: ((T > $worldTypeName > $$o) > $worldTypeName > $$o))."),
        annotatedTHF(s"thf(mexists_def, definition, mexists = ( ^ [T:$$tType, A:T>$worldTypeName>$$o, W:$worldTypeName]: ? [X:T]: ((eiw @ T @ X @ W) & (A @ X @ W)))).")
      )
    }

    lazy val polyAxiomTable: Map[FrameCondition, Option[TPTP.THF.Type => TPTP.AnnotatedFormula]] = Map(
      ConditionK -> None,
      ConditionT -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_reflexive, axiom, ![W:$worldTypeName,X:${ty.pretty}]: (mrel @ ${ty.pretty} @ X @ W @ W))."
      )),
      ConditionB -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_symmetric, axiom, ![W:$worldTypeName, V:$worldTypeName,X:${ty.pretty}]: ((mrel @ ${ty.pretty} @ X @ W @ V) => (mrel @ ${ty.pretty} @ X @ V @ W)))."
      )),
      ConditionD -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_serial, axiom, ![W:$worldTypeName,X:${ty.pretty}]: ?[V:$worldTypeName]: (mrel @ ${ty.pretty} @ X @ W @ V))."
      )),
      Condition4 -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_transitive, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName,X:${ty.pretty}]: (((mrel @ ${ty.pretty} @ X @ W @ V) & (mrel @ ${ty.pretty} @ X @ V @ U)) => (mrel @ ${ty.pretty} @ X @ W @ U)))."
      )),
      Condition5 -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_euclidean, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName,X:${ty.pretty}]: (((mrel @ ${ty.pretty} @ X @ W @ U) & (mrel @ ${ty.pretty} @ X @ W @ V)) => (mrel @ ${ty.pretty} @ X @ U @ V)))."
      ))
    )
    lazy val monoAxiomTable: Map[FrameCondition, Option[TPTP.THF.Type => TPTP.AnnotatedFormula]] = Map(
      ConditionK -> None,
      ConditionT -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_reflexive, axiom, ![W:$worldTypeName,X:${ty.pretty}]: (mrel_${serializeType(ty)} @ X @ W @ W))."
      )),
      ConditionB -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_symmetric, axiom, ![W:$worldTypeName, V:$worldTypeName,X:${ty.pretty}]: ((mrel_${serializeType(ty)} @ X @ W @ V) => (mrel_${serializeType(ty)} @ X @ V @ W)))."
      )),
      ConditionD -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_serial, axiom, ![W:$worldTypeName,X:${ty.pretty}]: ?[V:$worldTypeName]: (mrel_${serializeType(ty)} @ X @ W @ V))."
      )),
      Condition4 -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_transitive, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName,X:${ty.pretty}]: (((mrel_${serializeType(ty)} @ X @ W @ V) & (mrel_${serializeType(ty)} @ X @ V @ U)) => (mrel_${serializeType(ty)} @ X @ W @ U)))."
      )),
      Condition5 -> Some(ty => annotatedTHF(
        s"thf(mrel_${serializeType(ty)}_euclidean, axiom, ![W:$worldTypeName,V:$worldTypeName,U:$worldTypeName,X:${ty.pretty}]: (((mrel_${serializeType(ty)} @ X @ W @ U) & (mrel_${serializeType(ty)} @ X @ W @ V)) => (mrel_${serializeType(ty)} @ X @ U @ V)))."
      ))
    )

    /* enumeration of frame classes BEGIN */
    sealed abstract class FrameCondition
    final case object ConditionK extends FrameCondition
    final case object ConditionD extends FrameCondition
    final case object ConditionT extends FrameCondition
    final case object ConditionB extends FrameCondition
    final case object Condition4 extends FrameCondition
    final case object Condition5 extends FrameCondition

    sealed abstract class Logic
    final case object K extends Logic
    final case object K4 extends Logic
    final case object K5 extends Logic
    final case object KB extends Logic
    final case object K45 extends Logic
    final case object KB5 extends Logic
    final case object D extends Logic
    final case object D4 extends Logic
    final case object D5 extends Logic
    final case object D45 extends Logic
    final case object DB extends Logic
    final case object T extends Logic
    final case object B extends Logic
    final case object S4 extends Logic
    final case object S5 extends Logic
    /* enumeration of frame classes END */

    private[this] def logicToConditions(logic: Logic): Seq[FrameCondition] = logic match {
      case K => Seq(ConditionK)
      case K4 => Seq(ConditionK, Condition4)
      case K5 => Seq(ConditionK, Condition5)
      case KB => Seq(ConditionK, ConditionB)
      case K45 => Seq(ConditionK, Condition4, Condition5)
      case KB5 => Seq(ConditionK, ConditionB, Condition5)
      case D => Seq(ConditionK, ConditionD)
      case D4 => Seq(ConditionK, ConditionD, Condition4)
      case D5 => Seq(ConditionK, ConditionD, Condition5)
      case D45 => Seq(ConditionK, ConditionD, Condition4, Condition5)
      case DB => Seq(ConditionK, ConditionD, ConditionB)
      case T => Seq(ConditionK, ConditionT)
      case B => Seq(ConditionK, ConditionB)
      case S4 => Seq(ConditionK, ConditionT, Condition4)
      case S5 => Seq(ConditionK, ConditionT, Condition4, Condition5) // 4 is redundant, but might be helpful
    }
  }
}
