package leo.modules.embeddings

import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, THF}

/**
 * Embedding of Carmo and Jones' DDL logic, based on the article
 * "Faithful Semantical Embedding of a Dyadic Deontic Logic in HOL"
 * by Christoph Benzmüller, Ali Farjami and Xavier Parent, 2018.
 *
 * @see [[https://xavierparent.co.uk/pdf/article-final.pdf]]
 */
object CarmoJonesDDL extends Embedding {
  object CarmoJonesEmbeddingsOption extends Enumeration {
    final val MONOMORPHIC, POLYMORPHIC = Value
  }

  override final type OptionType = CarmoJonesEmbeddingsOption.type

  override final def name: String = "$$ddl"

  override final def version: String = "1.0"

  override final def embeddingParameter: CarmoJonesEmbeddingsOption.type = CarmoJonesEmbeddingsOption

  override final def generateSpecification(specs: Map[String, String]): TPTP.THFAnnotated = ???

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[CarmoJonesEmbeddingsOption.Value]): TPTP.Problem =
    new DDLEmbeddingImpl(problem, embeddingOptions).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class DDLEmbeddingImpl(problem: TPTP.Problem, embeddingsOptions: Set[CarmoJonesEmbeddingsOption.Value]) {
    import CarmoJonesEmbeddingsOption._

    private[this] val worldType: String = "ddlworld"
    @inline private[this] def cworldType: THF.Formula = str2Fun(worldType)
    private[this] val valid: String = "ddlvalid"
    @inline private[this] def cvalid: THF.Formula = str2Fun(valid)


    def apply(): TPTP.Problem = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val formulas = problemTHF.formulas
      val (spec, properFormulas) = splitInput(formulas)
      //      createState(spec)
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
          thf(s"^[W: $worldType]: $f")

        /* ######################################### */
        /* Standard cases: Recurse embedding. */
        case THF.FunctionTerm(f, args) =>
          val convertedArgs = args.map(convertFormula)
          THF.FunctionTerm(f, convertedArgs)

        case THF.UnaryFormula(connective, body) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedBody: TPTP.THF.Formula = convertFormula(body)
          THF.BinaryFormula(App, convertedConnective, convertedBody)

        case THF.BinaryFormula(App, left, right) =>
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, convertedLeft, convertedRight)

        /* The following case also subsumes where `connective` is a non-classical connective. */
        case THF.BinaryFormula(connective, left, right) =>
          val convertedConnective: TPTP.THF.Formula = convertConnective(connective)
          val convertedLeft: TPTP.THF.Formula = convertFormula(left)
          val convertedRight: TPTP.THF.Formula = convertFormula(right)
          THF.BinaryFormula(App, THF.BinaryFormula(App, convertedConnective, convertedLeft), convertedRight)

        case THF.DistinctObject(_) => formula

        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    private[this] val boxConnective: String = "$$box"
    private[this] val diaConnective: String = "$$dia"
    private[this] val obligationConnective: String = "$$obl"

    private[this] val not: String = "ddlnot"
    private[this] val equiv: String = "ddlequiv"
    private[this] val impl: String = "ddlimpl"
    private[this] val i_f: String = "ddlif"
    private[this] val niff: String = "ddlniff"
    private[this] val nor: String = "ddlnor"
    private[this] val nand: String = "ddlnand"
    private[this] val or: String = "ddlor"
    private[this] val and: String = "ddland"
    private[this] val box: String = "ddlbox"
    private[this] val dia: String = "ddldia"
    private[this] val obligation: String = "ddlobl"

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
        /// Non-classical connectives BEGIN
        // Box operator
        case THF.NonclassicalBox(index) => index match {
          case None => str2Fun(box)
          case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
        }
        // Diamond operator
        case THF.NonclassicalDiamond(index) => index match {
          case None => str2Fun(dia)
          case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
        }
        case THF.NonclassicalLongOperator(name, parameters) =>
          parameters match {
            case Seq() => name match {
              case `boxConnective` => str2Fun(box)
              case `diaConnective` => str2Fun(dia)
              case `obligationConnective` => str2Fun(obligation)
            }
            case _ => throw new EmbeddingException(s"Unsupported connective in $name: '${connective.pretty}'. ")
          }
        /// Non-classical connectives END
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
          if (f == "$o") THF.BinaryFormula(THF.FunTyConstructor, cworldType, typ)
          else typ

        case THF.BinaryFormula(connective, left, right) =>
          val convertedLeft = convertType(left)
          val convertedRight = convertType(right)
          THF.BinaryFormula(connective, convertedLeft, convertedRight)

        case _ => throw new EmbeddingException(s"Unexpected type expression in type: '${typ.pretty}'")
      }
    }


    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($worldType, type, $worldType: $$tType).")
    }
    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $worldType > $worldType > $$o).")
    }

    private[this] def mglobalTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${valid}_type, type, ${valid}: ($worldType > $$o) > $$o)."),
        annotatedTHF(s"thf(${valid}_def, definition, ${valid} = (^ [Phi: $worldType > $$o]: ![W: $worldType]: (Phi @ W)) ).")
      )
    }
    private[this] def connectivesTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${not}_type, type , ( $not: ($worldType>$$o)>$worldType>$$o) )."),
        annotatedTHF(s"thf(${and}_type, type , ( $and: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o) )."),
        annotatedTHF(s"thf(${or}_type, type , ( $or: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o) )."),
        annotatedTHF(s"thf(${impl}_type, type , ( $impl: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o) )."),
        annotatedTHF(s"thf(${equiv}_type, type , ( $equiv: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o) )."),
        annotatedTHF(s"thf(${not}_def, definition , ( $not = (^ [A:$worldType>$$o,W:$worldType] : ~(A@W))))."),
        annotatedTHF(s"thf(${and}_def, definition , ( $and = (^ [A:$worldType>$$o,B:$worldType>$$o,W:$worldType] : ( (A@W) & (B@W) ))))."),
        annotatedTHF(s"thf(${or}_def, definition , ( $or = (^ [A:$worldType>$$o,B:$worldType>$$o,W:$worldType] : ( (A@W) | (B@W) ))))."),
        annotatedTHF(s"thf(${impl}_def, definition , ( $impl = (^ [A:$worldType>$$o,B:$worldType>$$o,W:$worldType] : ( (A@W) => (B@W) ))))."),
        annotatedTHF(s"thf(${equiv}_def, definition , ( $equiv = (^ [A:$worldType>$$o,B:$worldType>$$o,W:$worldType] : ( (A@W) <=> (B@W) )))).")
      )
    }



  }

}
