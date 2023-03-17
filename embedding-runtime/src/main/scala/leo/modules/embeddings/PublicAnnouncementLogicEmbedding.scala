package leo.modules.embeddings

import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, THF}

/**
 * Embedding of public announcement logic (PAL) based on
 * (1) "Automating Public Announcement Logic with Relativized Common Knowledge as a Fragment of HOL in LogiKEy"
 * by C. Benzmüller and S. Reiche, Journal of Logic and Computation. 2022.
 *
 * @see [[https://arxiv.org/abs/2111.01654]]
 */
object PublicAnnouncementLogicEmbedding extends Embedding {
  object PublicAnnouncementLogicEmbeddingParameter extends Enumeration { }

  override final type OptionType = PublicAnnouncementLogicEmbeddingParameter.type

  override final val name: String = "$$pal"
  override final val version: String = "1.0"
  override final def embeddingParameter: PublicAnnouncementLogicEmbeddingParameter.type = PublicAnnouncementLogicEmbeddingParameter

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated =  {
    import leo.modules.input.TPTPParser.annotatedTHF
    annotatedTHF(s"thf(logic_spec, logic, ($name == [ ] )).")
  }

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[PublicAnnouncementLogicEmbeddingParameter.Value]): TPTP.Problem =
    new PALEmbeddingImpl(problem).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class PALEmbeddingImpl(problem: TPTP.Problem) {

    private[this] val worldType: String = "palworld"
    @inline private[this] def cworldType: THF.Formula = str2Fun(worldType)
    private[this] val indexType: String = "palindex"
    private[this] val valid: String = "palvalid"
    @inline private[this] def cvalid: THF.Formula = str2Fun(valid)

    private[this] val domainType: String = s"($worldType > $$o)"
    private[this] val truthType: String = s"($domainType > $domainType)"

    def apply(): TPTP.Problem = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val formulas = problemTHF.formulas
      val (spec, properFormulas) = splitInput(formulas)
      createState(spec)
      val (typeFormulas, nonTypeFormulas) = properFormulas.partition(_.role == "type")
      val (definitionFormulas, otherFormulas) = nonTypeFormulas.partition(_.role == "definition")
      val convertedTypeFormulas = typeFormulas.map(convertTypeFormula)
      val convertedDefinitionFormulas = definitionFormulas.map(convertDefinitionFormula)
      val convertedOtherFormulas = otherFormulas.map(convertAnnotatedFormula)
      val generatedMetaFormulas: Seq[AnnotatedFormula] = generateMetaFormulas()

      val result = generatedMetaFormulas ++ convertedTypeFormulas ++ convertedDefinitionFormulas ++ convertedOtherFormulas
      TPTP.Problem(problem.includes, result, Map.empty)
    }

    def convertDefinitionFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), body)), annotations) =>
          TPTP.THFAnnotated(name, "definition", THF.Logical(THF.BinaryFormula(THF.Eq, THF.FunctionTerm(symbolName, Seq()), convertFormula(body))), annotations)
        case _ => throw new EmbeddingException(s"Unsupported definition formula: ${formula.pretty}")
      }
    }

    def convertAnnotatedFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Logical(formula), annotations) =>
          val convertedFormula0 = convertFormula(formula)
          val convertedFormula = THF.BinaryFormula(THF.App, cvalid, convertedFormula0)
          TPTP.THFAnnotated(name, role, TPTP.THF.Logical(convertedFormula), annotations)
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }

    private[this] def convertFormula(formula: TPTP.THF.Formula): TPTP.THF.Formula = {
      import TPTP.THF.App
      import leo.modules.input.TPTPParser.thf

      formula match {
        /* ######################################### */
        /* TPTP defined constants that need to be handled specially*/
        // Nullary: $true and $false -> (^[W:mworld]: $true) resp. (^[W:mworld]: $false)
        case THF.FunctionTerm(f, Seq()) if Seq("$true", "$false").contains(f) =>
          thf(s"^[D: $domainType, W: $worldType]: $f")

        case THF.NonclassicalPolyaryFormula(connective, args) =>
          val convertedConnective = connective match {
            case THF.NonclassicalBox(index) => index match {
              case Some(idx) => indexedKnowledge(idx)
              case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
            }
            case THF.NonclassicalLongOperator(cname, index, parameters) =>
              cname match {
                case `knowledgeConnective` =>
                  if (parameters.nonEmpty) throw new EmbeddingException(s"Illegal parameter specified for '$cname' in ${connective.pretty}.")
                  index match {
                    case Some(index0) => indexedKnowledge(index0)
                    case None => throw new IllegalArgumentException(s"Index parameter required for '$cname' in ${connective.pretty}.")
                  }
                case `commonKnowledgeConnective` =>
                  if (index.nonEmpty) throw new EmbeddingException(s"Illegal parameter specified for '$cname' in ${connective.pretty}.")
                  parameters match {
                  case Seq((THF.FunctionTerm("$$group", Seq()), THF.Tuple(elements))) if elements.nonEmpty =>
                    val indexes = elements.map {
                      case idx@THF.FunctionTerm(_, Seq()) => multiModal(idx)
                      case _ => throw new IllegalArgumentException(s"Illegal index values in parameter to '$cname': ${connective.pretty}")
                    }
                    val body0 = indexes.map(idx =>
                      THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, THF.BinaryFormula(THF.App, str2Fun("mrel"), idx), THF.Variable("W")), THF.Variable("V"))
                    )

                    def reduce0(l: THF.Formula, r: THF.Formula): THF.Formula = THF.BinaryFormula(THF.|, l, r)

                    val body: THF.Formula = body0.reduce(reduce0)
                    val rel = THF.QuantifiedFormula(THF.^, Seq(("W", cworldType), ("V", cworldType)), body)
                    THF.BinaryFormula(THF.App, str2Fun(common), rel)
                  case _ => throw new IllegalArgumentException(s"Illegal parameter specified for '$cname' in ${connective.pretty}.")
                }
                case `announcementConnective` =>
                  if (index.nonEmpty) throw new EmbeddingException(s"Illegal parameter specified for '$cname' in ${connective.pretty}.")
                  parameters match {
                    case Seq((THF.FunctionTerm("$$formula", Seq()), announcementFormula)) =>
                      val convertedAnnouncement = convertFormula(announcementFormula)
                      THF.BinaryFormula(THF.App, str2Fun(announcement), convertedAnnouncement)
                    case _ => throw new IllegalArgumentException(s"Illegal parameter specified for '$cname' in ${connective.pretty}.")
                  }
                case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
              }
          }
          val body = if (args.size == 1)  args.head else throw new EmbeddingException(s"Only unary connectives supported, but '${formula.pretty}' was given.")
          THF.BinaryFormula(THF.App, convertedConnective, convertFormula(body))

        /* ######################################### */
        /* Standard cases: Recurse embedding. */
        case THF.FunctionTerm(f, Seq()) =>
          val aOperator = thf(s"^[A: $domainType, D:$domainType, W:$worldType]: ((D @ W) & (A @ W))")
          THF.BinaryFormula(THF.App, aOperator, THF.FunctionTerm(f, Seq.empty))

        case THF.UnaryFormula(connective, body) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedBody: TPTP.THF.Formula = convertFormula(body)
          THF.BinaryFormula(App, convertedConnective, convertedBody)

        case THF.BinaryFormula(App, left, right) =>
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, convertedLeft, convertedRight)

        case THF.BinaryFormula(connective, left, right) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, THF.BinaryFormula(App, convertedConnective, convertedLeft), convertedRight)

        case THF.DistinctObject(_) => formula

        case THF.ConnectiveTerm(conn) => convertConnective(conn)

        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    private[this] val knowledgeConnective: String = "$$knows"
    private[this] val commonKnowledgeConnective: String = "$$common"
    private[this] val announcementConnective: String = "$$announce"


    private[this] val not: String = "palnot"
    private[this] val equiv: String = "palequiv"
    private[this] val impl: String = "palimpl"
    private[this] val i_f: String = "palif"
    private[this] val niff: String = "palniff"
    private[this] val nor: String = "palnor"
    private[this] val nand: String = "palnand"
    private[this] val or: String = "palor"
    private[this] val and: String = "paland"
    private[this] val announcement: String = "palannounce"
    private[this] val common: String = "palcommon"
    private[this] val knowledge: String = "palknowledge"


    private[this] def convertConnective(connective: TPTP.THF.Connective): THF.Formula = {
      connective match {
        case THF.~ => str2Fun(not)
        case THF.<=> => str2Fun(equiv)
        case THF.Impl => str2Fun(impl)
        case THF.<= => str2Fun(i_f)
        case THF.<~> => str2Fun(niff)
        case THF.~| => str2Fun(nor)
        case THF.~& => str2Fun(nand)
        case THF.| => str2Fun(or)
        case THF.& => str2Fun(and)
        case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
      }
    }

    private def convertTypeFormula(formula: AnnotatedFormula): AnnotatedFormula = {
      formula match {
        case TPTP.THFAnnotated(name, role, TPTP.THF.Typing(symbol, typ), annotations) =>
          val convertedTyping = TPTP.THF.Typing(symbol, convertType(typ))
          TPTP.THFAnnotated(name, role, convertedTyping, annotations)
        case TPTP.THFAnnotated(_, _, _, _) => throw new EmbeddingException(s"Unexpected error: Type conversion called on non-type-statement.")
        case _ => throw new EmbeddingException(s"Only embedding of THF files supported.")
      }
    }
    private def convertType(typ: TPTP.THF.Type): TPTP.THF.Type = {
      typ match {
        case THF.FunctionTerm(f, Seq()) =>
//          if (f == "$o") THF.BinaryFormula(THF.FunTyConstructor, THF.BinaryFormula(THF.FunTyConstructor, cworldType, typ), THF.BinaryFormula(THF.FunTyConstructor, cworldType, typ))
          if (f == "$o") THF.BinaryFormula(THF.FunTyConstructor, cworldType, typ)
          else typ

        case THF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertType(left)
          val convertedRight = convertType(right)
          THF.BinaryFormula(connective, convertedLeft, convertedRight)

        case _ => throw new EmbeddingException(s"Unexpected type expression in type: '${typ.pretty}'")
      }
    }


    private[this] def indexedKnowledge(index: THF.Formula): THF.Formula = {
      THF.BinaryFormula(THF.App, str2Fun(knowledge), multiModal(index))
    }

    import collection.mutable
    private[this] val modalOperators: mutable.Set[THF.FunctionTerm] = mutable.Set.empty
    private[this] def multiModal(index: THF.Formula): THF.FunctionTerm = {
      val index0: THF.FunctionTerm = index match {
        case THF.FunctionTerm(name, Seq()) => THF.FunctionTerm(s"#$name", Seq.empty)
        case _ => throw new EmbeddingException("Unsupported index")
      }
      modalOperators += index0
      index0
    }

    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty
      /////////////////////////////////////////////////////////////
      // First: Introduce world type
      result.append(worldTypeTPTPDef())
      // introduce index type
      result.append(indexTypeTPTPDef())
      // meta defs
      result.appendAll(accessibilityRelationMetaDefsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Introduce mrel
      result.append(indexedAccessibilityRelationTPTPDef())
      // add properties
      result.appendAll(accessibilityRelationPropsTPTPDef())
      // define index types
      modalOperators.foreach { index =>
        result.append(indexTPTPDef(index))
      }
      /////////////////////////////////////////////////////////////
      // Then: Define valid
      result.appendAll(validTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define connectives
      result.appendAll(connectivesTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define modal operators
      result.appendAll(modalOperatorsTPTPDef())
      /////////////////////////////////////////////////////////////
      // Return all
      result.toSeq
    }

    private[this] def unescapeTPTPName(name: String): String = {
      if (name.startsWith("'") && name.endsWith("'")) {
        name.tail.init
      } else name
    }
    private def escapeName(name: String): String = {
      val integerRegex = "^[+-]?[\\d]+$"
      if (name.matches(integerRegex)) name else escapeAtomicWord(name)
    }
    private def escapeAtomicWord(word: String): String = {
      val simpleLowerWordRegex = "^[a-z][a-zA-Z\\d_]*$"
      if (word.matches(simpleLowerWordRegex)) word
      else s"'${word.replace("\\","\\\\").replace("'", "\\'")}'"
    }

    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($worldType, type, $worldType: $$tType).")
    }
    private[this] def indexTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($indexType, type, $indexType: $$tType).")
    }

    private[this] def indexTPTPDef(index: THF.FunctionTerm): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      val name = s"${unescapeTPTPName(index.pretty)}_type"
      annotatedTHF(s"thf(${escapeName(name)}, type, ${index.pretty}: $indexType).")
    }

    private[this] def indexedAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $indexType > $worldType > $worldType > $$o).")
    }

    private[this] def accessibilityRelationMetaDefsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(paltrans_type, type, paltrans: ($worldType > $worldType > $$o) > $$o)."),
        annotatedTHF(s"thf(paltrans_def, definition, paltrans = (^[R:$worldType > $worldType > $$o]: ![X:$worldType, Y: $worldType, Z:$worldType]: (((R @ X @ Y) & (R @ Y @ Z)) => (R @ X @ Z))))."),
        annotatedTHF(s"thf(palsub_type, type, palsub: ($worldType > $worldType > $$o) > ($worldType > $worldType > $$o) > $$o)."),
        annotatedTHF(s"thf(palsub_def, definition, palsub = (^[R:$worldType > $worldType > $$o,Q: $worldType > $worldType > $$o]: ![X:$worldType, Y:$worldType]: ((R @ X @ Y) => (Q @ X @ Y))))."),
        annotatedTHF(s"thf(paltranscl_type, type, paltranscl: ($worldType > $worldType > $$o) > $worldType > $worldType > $$o)."),
        annotatedTHF(s"thf(paltranscl_def, definition, paltranscl = (^[R: $worldType > $worldType > $$o,X:$worldType, Y:$worldType]: ![Q:$worldType > $worldType > $$o]: ((paltrans @ Q) => ((palsub @ R @ Q) => (Q @ X @ Y)))))."),
      )

    }

    private[this] def accessibilityRelationPropsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(mrel_reflexive, axiom, ![I:$indexType, W:$worldType]: (mrel @ I @ W @ W))."),
        annotatedTHF(s"thf(mrel_transitive, axiom, ![I:$indexType, W:$worldType,V:$worldType,U:$worldType]: (((mrel @ I @ W @ V) & (mrel @ I @ V @ U)) => (mrel @ I @ W @ U)))."),
        annotatedTHF(s"thf(mrel_euclidean, axiom, ![I:$indexType, W:$worldType,V:$worldType,U:$worldType]: (((mrel @ I @ W @ U) & (mrel @ I @ W @ V)) => (mrel @ I @ U @ V))).")
      )

    }

    private[this] def validTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${valid}_type, type, $valid: $truthType > $$o)."),
        annotatedTHF(s"thf(${valid}_def, definition, $valid = (^ [Phi: $truthType]: ![D: $domainType, W: $worldType]: ((D @ W) => (Phi @ D @ W))) ).")
      )
    }
    private[this] def connectivesTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${not}_type, type , ( $not: $truthType>$truthType) )."),
        annotatedTHF(s"thf(${and}_type, type , ( $and: $truthType>$truthType>$truthType) )."),
        annotatedTHF(s"thf(${or}_type, type , ( $or: $truthType>$truthType>$truthType) )."),
        annotatedTHF(s"thf(${impl}_type, type , ( $impl: $truthType>$truthType>$truthType) )."),
        annotatedTHF(s"thf(${equiv}_type, type , ( $equiv: $truthType>$truthType>$truthType) )."),
        annotatedTHF(s"thf(${not}_def, definition , ( $not = (^ [A:$truthType,D:$domainType,W:$worldType] : ~(A@D@W))))."),
        annotatedTHF(s"thf(${and}_def, definition , ( $and = (^ [A:$truthType,B:$truthType,D:$domainType,W:$worldType] : ( (A@D@W) & (B@D@W) ))))."),
        annotatedTHF(s"thf(${or}_def, definition , ( $or = (^ [A:$truthType,B:$truthType,D:$domainType,W:$worldType] : ( (A@D@W) | (B@D@W) ))))."),
        annotatedTHF(s"thf(${impl}_def, definition , ( $impl = (^ [A:$truthType,B:$truthType,D:$domainType,W:$worldType] : ( (A@D@W) => (B@D@W) ))))."),
        annotatedTHF(s"thf(${equiv}_def, definition , ( $equiv = (^ [A:$truthType,B:$truthType,D:$domainType,W:$worldType] : ( (A@D@W) <=> (B@D@W) )))).")
      )
    }

    private[this] def modalOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${knowledge}_type, type, $knowledge: $indexType > $truthType>$truthType )."),
        annotatedTHF(s"thf(${knowledge}_def, definition, ( $knowledge = (^ [I:$indexType, Phi:$truthType,D:$domainType,W:$worldType]: ! [V:$worldType]: ( ((D @ V) & (mrel @ I @ W @ V)) => (Phi @ D @ V) ))))."),
        annotatedTHF(s"thf(${common}_type, type, $common: ($worldType > $worldType > $$o) > $truthType>$truthType )."),
        annotatedTHF(s"thf(${common}_def, definition, ( $common = (^ [R:$worldType > $worldType > $$o, Phi:$truthType,D:$domainType,W:$worldType]: ! [V:$worldType]: ( ((D @ V) & ((paltranscl @ R) @ W @ V)) => (Phi @ D @ V) ))))."),
        annotatedTHF(s"thf(${announcement}_type, type, $announcement: $truthType>$truthType>$truthType )."),
        annotatedTHF(s"thf(${announcement}_def, definition, ( $announcement = (^ [Ann:$truthType,Phi:$truthType,D:$domainType,W:$worldType]: ( (Ann @ D @ W) => (Phi @ (^[X:$worldType]: ((D @ X) & (Ann @ D @ X))) @ W) )))).")
      )
    }

    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////

    private[this] def createState(spec: TPTP.AnnotatedFormula): Unit = {
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(`name`, Seq()),t@THF.Tuple(spec0)))  =>
          if (spec0.nonEmpty) throw new EmbeddingException(s"Logic parameters not supported by logic '$name' but ${t.pretty} was given.")
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

}
