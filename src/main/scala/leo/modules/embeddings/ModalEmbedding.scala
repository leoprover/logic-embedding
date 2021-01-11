package leo
package modules
package embeddings

import datastructures.{FlexMap, TPTP}
import TPTP.{AnnotatedFormula, THF}

object ModalEmbedding {
  type EmbeddingOption = EmbeddingOption.EmbeddingOption
  final object EmbeddingOption extends Enumeration {
    type EmbeddingOption = Value
    final val MONOMORPHIC, POLYMORPHIC, SEMANTICAL, SYNTACTICAL = Value
  }

  final def apply(problem: Seq[AnnotatedFormula],
                  embeddingOptions: Set[EmbeddingOption] = Set.empty): Seq[AnnotatedFormula] =
    new ModalEmbeddingImpl().apply(problem, embeddingOptions)

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class ModalEmbeddingImpl extends Embedding[EmbeddingOption] {

    ///////////////////////////////////////////////////////////////////
    private final val state = FlexMap.apply()

    // Embedding options
    private final val POLYMORPHISM = state.createKeyWithDefault[Nothing, Boolean](default = false)

    private final val EMBEDDING_SYNTACTICAL = false
    private final val EMBEDDING_SEMANTICAL = true
    private final val EMBEDDINGTYPE = state.createKeyWithDefault[Nothing, Boolean](default = EMBEDDING_SEMANTICAL)

    // Semantics dimensions
    private final val RIGIDITY_RIGID = true
    private final val RIGIDITY_FLEXIBLE = false
    private final val RIGIDITY = state.createKey[String, Boolean]()
    state(RIGIDITY) += ("$o" -> RIGIDITY_FLEXIBLE)

    private final val CONSEQUENCE_GLOBAL = true
    private final val CONSEQUENCE_LOCAL = false
    private final val CONSEQUENCE = state.createKey[String, Boolean]()

    private final val DOMAIN_CONSTANT = 0
    private final val DOMAIN_VARYING = 1
    private final val DOMAIN_CUMULATIVE = 2
    private final val DOMAIN_DECREASING = 3
    private final val DOMAIN = state.createKey[String, Int]()

    private final val MODALS = state.createKey[String, Seq[String]]()
    ////////////////////////////////////////////////////////////////////

    def apply(problem: Seq[AnnotatedFormula], embeddingOptions: Set[EmbeddingOption]): Seq[AnnotatedFormula] = {
      val (spec, remainingFormulas) = splitInput(problem)
      createState(spec, embeddingOptions)
      val (typeFormulas, nonTypeFormulas) = remainingFormulas.partition(_.role == "type")
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedOtherFormulas = nonTypeFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      generatedMetaFormulas ++ convertedTypeFormulas ++ convertedOtherFormulas
    }

    def convertAnnotatedFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Logical(formula), annotations) =>
          val convertedFormula0 = convertFormula(formula)
          val convertedFormula = state(CONSEQUENCE)(name) match {
            case CONSEQUENCE_GLOBAL => THF.BinaryFormula(THF.App, mglobal, convertedFormula0)
            case CONSEQUENCE_LOCAL => THF.BinaryFormula(THF.App, mlocal, convertedFormula0)
          }
          TPTP.THFAnnotated(name, role, TPTP.THF.Logical(convertedFormula), annotations)
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private def mkLambda(variable: THF.TypedVariable, body: THF.Formula): THF.Formula = {
      THF.QuantifiedFormula(THF.^, Seq(variable), body)
    }

    private def mkSingleQuantified(quantifier: THF.Quantifier)(variable: THF.TypedVariable, acc: THF.Formula): THF.Formula = {
      val convertedVariable: THF.TypedVariable = (variable._1, convertType(variable._2))
      val convertedQuantifier: THF.Formula =
        if (state(POLYMORPHISM)()) THF.BinaryFormula(THF.App, convertQuantifier(quantifier, variable._2, convertedVariable._2), convertedVariable._2)
        else convertQuantifier(quantifier, variable._2, convertedVariable._2)
      THF.BinaryFormula(THF.App, convertedQuantifier, mkLambda(convertedVariable, acc))
    }

    private def convertFormula(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
      import TPTP.THF.App
      formula match {
        case THF.FunctionTerm("$box", Seq()) => mbox
        case THF.FunctionTerm("$dia", Seq()) => mdia

        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertFormula)
          THF.FunctionTerm(f, convertedArgs)

        case THF.QuantifiedFormula(quantifier, variableList, body) =>
          val convertedBody = convertFormula(body)
          variableList.foldRight(convertedBody)(mkSingleQuantified(quantifier))

        case THF.Variable(_) => formula

        case THF.UnaryFormula(connective, body) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedBody: TPTP.THF.Formula = convertFormula(body)
          THF.BinaryFormula(App, convertedConnective, convertedBody)

        case THF.BinaryFormula(App, left, right) =>
          left match {
            case THF.FunctionTerm("$box_int", Seq()) =>
              right match {
                case THF.NumberTerm(TPTP.Integer(value)) => multiModal(value.toString)
                  THF.BinaryFormula(App, mbox, THF.FunctionTerm(value.toString, Seq.empty)) // TODO
              }
            case THF.FunctionTerm("$dia_int", Seq()) => ???
            case THF.FunctionTerm("$box_i", Seq()) => ???
            case THF.FunctionTerm("$dia_i", Seq()) => ???
            case _ =>
              val convertedLeft: TPTP.THF.Formula = convertFormula(left)
              val convertedRight: TPTP.THF.Formula = convertFormula(right)
              THF.BinaryFormula(App, convertedLeft, convertedRight)
          }

        case THF.BinaryFormula(connective, left, right) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, convertedConnective, THF.BinaryFormula(App, convertedLeft, convertedRight))

        case THF.ConnectiveTerm(conn) => convertConnective(conn)

        case THF.Tuple(elements) =>
          val convertedElements: Seq[TPTP.THF.Formula] = elements.map(convertFormula)
          THF.Tuple(convertedElements)

        case THF.ConditionalTerm(condition, thn, els) =>
          val convertedCondition: TPTP.THF.Formula = convertFormula(condition)
          val convertedThn: TPTP.THF.Formula = convertFormula(thn)
          val convertedEls: TPTP.THF.Formula = convertFormula(els)
          THF.ConditionalTerm(convertedCondition, convertedThn, convertedEls)

        case THF.LetTerm(typing, binding, body) => // This will probably change as the parse tree of LetTerms will still change.
          val convertedTyping: Map[String, TPTP.THF.Type] = typing.map(a => (a._1, convertType(a._2)))
          val convertedBinding: Seq[(TPTP.THF.Formula, TPTP.THF.Formula)]  = binding.map(a => (convertFormula(a._1), convertFormula(a._2)))
          val convertedBody = convertFormula(body)
          THF.LetTerm(convertedTyping, convertedBinding, convertedBody)
        case THF.DistinctObject(_) => formula
        case THF.NumberTerm(_) => formula
      }
    }

    private def convertConnective(connective: TPTP.THF.Connective): THF.Formula = {
      val name = connective match {
        case THF.~ => "mnot"
        case THF.!! => "mforall"
        case THF.?? => "mexists"
        case THF.@@+ => "mchoice"
        case THF.@@- => "mdesc"
        case THF.@= => "meq"
        case THF.Eq => "meq"
        case THF.Neq => "mneq"
        case THF.<=> => "mequiv"
        case THF.Impl => "mimpl"
        case THF.<= => "mif"
        case THF.<~> => "mniff"
        case THF.~| => "mnor"
        case THF.~& => "mnand"
        case THF.| => "mor"
        case THF.& => "mand"
        case THF.App => throw new EmbeddingException(s"An unexpected error occurred, this is considered a bug. Please report it :-)")
        case THF.:= => throw new EmbeddingException(s"Unexpected assignment operator used as connective.")
        case _ => throw new EmbeddingException(s"Unexpected type constructor used as connective: '${connective.pretty}'")
        //      case THF.FunTyConstructor => ???
        //      case THF.ProductTyConstructor => ???
        //      case THF.SumTyConstructor => ???
      }
      THF.FunctionTerm(name, Seq.empty)
    }

    private def convertQuantifier(quantifier: TPTP.THF.Quantifier, typ: TPTP.THF.Type, convertedType: TPTP.THF.Type): THF.Formula = {
      val name = quantifier match {
        case THF.! =>
          try {
            state(DOMAIN)(typ.pretty) match {
              case DOMAIN_CONSTANT => if (state(POLYMORPHISM)()) "mforall_const" else s"mforall_const_${serializeType(convertedType)}"
              case _ => // all three other cases
                if (state(POLYMORPHISM)()) "mforall_vary" else s"mforall_vary_${serializeType(convertedType)}"
            }
          } catch {
            case _: NoSuchElementException => throw new EmbeddingException(s"Undefined domain semantics for type '${typ.pretty}'. Maybe a default value was omitted?")
          }

        case THF.? =>
          try {
            state(DOMAIN)(typ.pretty) match {
              case DOMAIN_CONSTANT => if (state(POLYMORPHISM)()) "mexists_const" else s"mexists_const_${serializeType(convertedType)}"
              case _ => // all three other cases
                if (state(POLYMORPHISM)()) "mexists_vary" else s"mexists_vary_${serializeType(convertedType)}"
            }
          } catch {
            case _: NoSuchElementException => throw new EmbeddingException(s"Undefined domain semantics for type '${typ.pretty}'. Maybe a default value was omitted?")
          }
        case THF.^ => "mlambda"
        case THF.@+ => "mchoice"
        case THF.@- => "mdescription"
        case _ => throw new EmbeddingException(s"Unexpected type quantifier used as term quantifier: '${quantifier.pretty}'")
      }
      THF.FunctionTerm(name, Seq.empty)
    }

    private[this] def mbox: THF.Formula = THF.FunctionTerm("mbox", Seq.empty)
    private[this] def mdia: THF.Formula = THF.FunctionTerm("mdia", Seq.empty)
    private[this] def mbox_i: THF.Formula = THF.FunctionTerm("mbox_i", Seq.empty)
    private[this] def mdia_i: THF.Formula = THF.FunctionTerm("mdia_i", Seq.empty)
    private[this] def mbox_int: THF.Formula = THF.FunctionTerm("mbox_int", Seq.empty)
    private[this] def mdia_int: THF.Formula = THF.FunctionTerm("mdia_int", Seq.empty)

    private[this] def mglobal: THF.Formula = THF.FunctionTerm("mglobal", Seq.empty)
    private[this] def mlocal: THF.Formula =  THF.FunctionTerm("mlocal", Seq.empty)


    private def convertTypeFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Typing(typeName, typ), annotations) =>
          val convertedTyping = TPTP.THF.Typing(typeName, convertType(typ))
          TPTP.THFAnnotated(name, role, convertedTyping, annotations)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertType) ///TODO What to do with those?
          if (state(RIGIDITY)(f)) THF.FunctionTerm(f, convertedArgs)
          else THF.BinaryFormula(THF.FunTyConstructor, worldType, THF.FunctionTerm(f, convertedArgs))

        case THF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertType(left)
          val convertedRight = convertType(right)
          THF.BinaryFormula(connective, convertedLeft, convertedRight)

        case THF.Tuple(elements) =>
          val convertedElements = elements.map(convertType)
          THF.Tuple(convertedElements)

        // TODO: Could support polymorphic types
        // case THF.QuantifiedFormula(quantifier, variableList, body) =>
        // case THF.Variable(name) =>

        case _ => throw new EmbeddingException(s"Unexpected type expression in type: '${typ.pretty}'")
      }
    }

    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable
      import modules.input.TPTPParser.annotatedTHF

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty

      // First: Introduce world type
      result.append(worldTypeTPTPDef())

      // Then: Introduce mrel (as relation or as collection of relations)
      if (isMultiModal) result.append(indexedAccessibilityRelationTPTPDef("sometype")) // TODO
      else result.append(simpleAccessibilityRelationTPTPDef())

      // Then: Define mglobal/mlocal
      state.getDefault(CONSEQUENCE) match {
        case Some(consequence) => consequence match { // Add default and the other one if used
          case CONSEQUENCE_GLOBAL =>
            result.appendAll(mglobalTPTPDef())
            if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mlocalTPTPDef())
          case CONSEQUENCE_LOCAL =>
            result.appendAll(mlocalTPTPDef())
            if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mglobalTPTPDef())
        }
        case None => // Add only those used
          if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mlocalTPTPDef())
          if (state(CONSEQUENCE).exists(_._2 == CONSEQUENCE_LOCAL)) result.appendAll(mglobalTPTPDef())
      }

      // Then: Define connectives and modal operators
      result.appendAll(connectivesTPTPDef())
      if (isMultiModal) result.appendAll(indexedModalOperatorsTPTPDef("sometype")) // TODO
      else result.appendAll(simpleModalOperatorsTPTPDef())

      // Then: Give mrel properties (sem/syn)
      // write used properties and assign (if semantical)
      // or write syntactical axioms (if syntactical)

      // Then: Define quantifiers (TH0/TH1)

      // Then: Define quantifier restrictions (if cumul/decr)

      // Return all
      result.toSeq
    }

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF("thf(mworld_type, type, mworld: $tType).")
    }

    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF("thf(mrel_type, type, mrel: mworld > mworld > $$o).")
    }

    private[this] def indexedAccessibilityRelationTPTPDef(typ: String): TPTP.AnnotatedFormula = {
      import modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $typ > mworld > mworld > $$o).")
    }

    private[this] def mglobalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF("thf(mglobal_type, type, mglobal: (mworld > $o) > $o)."),
        annotatedTHF("thf(mglobal_def, type, mglobal = (^ [Phi: mworld > $o]: ![W: mworld]: (Phi @ W)) ).")
      )
    }

    private[this] def mlocalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF("thf(mactual_type, type, mactual: mworld)."),
        annotatedTHF("thf(mlocal_type, type, mglobal: (mworld > $o) > $o)."),
        annotatedTHF("thf(mlocal_def, type, mglobal = (^ [Phi: mworld > $o]: (Phi @ mactual)) ).")
      )
    }

    private[this] def connectivesTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF("thf(mnot_type, type , ( mnot: (mworld>$o)>mworld>$o) )."),
        annotatedTHF("thf(mand_type, type , ( mand: (mworld>$o)>(mworld>$o)>mworld>$o) )."),
        annotatedTHF("thf(mor_type, type , ( mor: (mworld>$o)>(mworld>$o)>mworld>$o) )."),
        annotatedTHF("thf(mimplies_type, type , ( mimplies: (mworld>$o)>(mworld>$o)>mworld>$o) )."),
        annotatedTHF("thf(mequiv_type, type , ( mequiv: (mworld>$o)>(mworld>$o)>mworld>$o) )."),
        annotatedTHF("thf(mnot_def, definition , ( mnot = (^ [A:mworld>$o,W:mworld] : ~(A@W))))."),
        annotatedTHF("thf(mand_def, definition , ( mand = (^ [A:mworld>$o,B:mworld>$o,W:mworld] : ( (A@W) & (B@W) ))))."),
        annotatedTHF("thf(mor_def, definition , ( mor = (^ [A:mworld>$o,B:mworld>$o,W:mworld] : ( (A@W) | (B@W) ))))."),
        annotatedTHF("thf(mimplies_def, definition , ( mimplies = (^ [A:mworld>$o,B:mworld>$o,W:mworld] : ( (A@W) => (B@W) ))))."),
        annotatedTHF("thf(mequiv_def, definition , ( mequiv = (^ [A:mworld>$o,B:mworld>$o,W:mworld] : ( (A@W) <=> (B@W) )))).")
      )
    }

    private[this] def simpleModalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF("thf(mbox_type, type, mbox: (mworld>$o)>mworld>$o )."),
        annotatedTHF("thf(mbox_def, definition, ( mbox = (^ [Phi:mworld>$o, W:mworld]: ![V:mworld]: ( (mrel @ W @ V) => (Phi @ V) )))).")
      )
    }

    private[this] def indexedModalOperatorsTPTPDef(typ: String): Seq[TPTP.AnnotatedFormula] = {
      import modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mbox_type, type, mbox: $typ > (mworld>$$o)>mworld>$$o )."),
        annotatedTHF(s"thf(mbox_def, definition, ( mbox = (^ [R:$typ, A:mworld>$$o,W:mworld]: ! [V:mworld]: ( (mrel@R@W@V) => (A@V) )))).")
      )
    }

    private[this] def worldType: TPTP.THF.Type = {
      THF.FunctionTerm("mworld", Seq.empty)
    }


    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////
    import collection.mutable
    private[this] final val modalOperators: mutable.Buffer[String] = mutable.Buffer.empty
    private[this] def isMultiModal: Boolean = modalOperators.nonEmpty
    private[this] def multiModal(identifier: String): Unit = modalOperators += identifier


    private[this] def createState(spec: TPTP.AnnotatedFormula, options: Set[EmbeddingOption]): Unit = {
      if (options contains EmbeddingOption.POLYMORPHIC) state(POLYMORPHISM) += (() -> true)
      if (options contains EmbeddingOption.SYNTACTICAL) state(EMBEDDINGTYPE) += (() -> EMBEDDING_SYNTACTICAL)

      assert(spec.role == "logic")
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.:=, THF.FunctionTerm("$modal", Seq()),THF.Tuple(spec0))) =>
          spec0 foreach {
            case THF.BinaryFormula(THF.:=, THF.FunctionTerm(propertyName, Seq()), rhs) =>
              propertyName match {
                case "$constants" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$rigid") => state.setDefault(RIGIDITY, RIGIDITY_RIGID)
                    case Some("$flexible") => state.setDefault(RIGIDITY, RIGIDITY_FLEXIBLE)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, rigidity) =>
                    rigidity match {
                      case "$rigid" => state(RIGIDITY) += (name -> RIGIDITY_RIGID)
                      case "$flexible" => state(RIGIDITY) += (name -> RIGIDITY_FLEXIBLE)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$rigidity'")
                    }
                  }
                case "$quantification" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$constant") => state.setDefault(DOMAIN, DOMAIN_CONSTANT)
                    case Some("$varying") => state.setDefault(DOMAIN, DOMAIN_VARYING)
                    case Some("$cumulative") => state.setDefault(DOMAIN, DOMAIN_CUMULATIVE)
                    case Some("$decreasing") => state.setDefault(DOMAIN, DOMAIN_DECREASING)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, quantification) =>
                    quantification match {
                      case "$constant" => state(DOMAIN) += (name -> DOMAIN_CONSTANT)
                      case "$varying" => state(DOMAIN) += (name -> DOMAIN_VARYING)
                      case "$cumulative" => state(DOMAIN) += (name -> DOMAIN_CUMULATIVE)
                      case "$decreasing" => state(DOMAIN) += (name -> DOMAIN_DECREASING)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$quantification'")
                    }
                  }
                case "$consequence" =>
                  val (default, map) = parseRHS(rhs)
                  default match {
                    case Some("$local") => state.setDefault(CONSEQUENCE, CONSEQUENCE_LOCAL)
                    case Some("$global") => state.setDefault(CONSEQUENCE, CONSEQUENCE_GLOBAL)
                    case None => // Do nothing, no default
                    case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$default'")
                  }
                  map foreach { case (name, consequence) =>
                    consequence match {
                      case "$local" => state(CONSEQUENCE) += (name -> CONSEQUENCE_LOCAL)
                      case "$global" => state(CONSEQUENCE) += (name -> CONSEQUENCE_GLOBAL)
                      case _ => throw new EmbeddingException(s"Unrecognized semantics option: '$consequence'")
                    }
                  }
                case "$modalities" => val (default, map) = parseListRHS(rhs)
                  if (default.nonEmpty) state.setDefault(MODALS, default)
                  map foreach { case (name, modalspec) =>
                    if (modalspec.nonEmpty) state(MODALS) += (name -> modalspec)
                  }
                case _ => throw new EmbeddingException(s"Unknown modal logic semantics property '$propertyName'")
              }
            case s => throw new EmbeddingException(s"Malformed logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

}
