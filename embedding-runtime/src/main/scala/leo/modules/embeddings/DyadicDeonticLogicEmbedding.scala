package leo.modules.embeddings

import leo.datastructures.TPTP
import TPTP.{AnnotatedFormula, THF}

/**
 * Embedding of various dyadic deontic logics (DDLs):
 * (1) Carmo and Jones' DDL logic, based on the article
 * "Faithful Semantical Embedding of a Dyadic Deontic Logic in HOL"
 * by Christoph Benzmüller, Ali Farjami and Xavier Parent, 2018.
 *
 * (2) Aqvist systems E, F, G, embedding based on
 * "Åqvist’s Dyadic Deontic Logic E in HOL"
 * by C. Benzmüller, A. Farjami and X. Parent, Journal of Applied logics
 *
 * @see [[https://xavierparent.co.uk/pdf/article-final.pdf]]
 * @see [[https://xavierparent.co.uk/pdf/eHOL.pdf]]
 */
object DyadicDeonticLogicEmbedding extends Embedding {
  object CarmoJonesEmbeddingsOption extends Enumeration { }

  override final type OptionType = CarmoJonesEmbeddingsOption.type

  override final val name: String = "$$ddl"

  override final val version: String = "1.0"

  override final def embeddingParameter: CarmoJonesEmbeddingsOption.type = CarmoJonesEmbeddingsOption

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

  override final def apply(problem: TPTP.Problem, embeddingOptions: Set[CarmoJonesEmbeddingsOption.Value]): TPTP.Problem =
    new DDLEmbeddingImpl(problem).apply()

  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  // The embedding
  /////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////
  private[this] final class DDLEmbeddingImpl(problem: TPTP.Problem) {

    private[this] var ddlSystem: DDLSystem = Unknown
    sealed abstract class DDLSystem
    final case object Unknown extends DDLSystem
    final case object AqvistE extends DDLSystem
    final case object AqvistF extends DDLSystem
    final case object AqvistG extends DDLSystem
    final case object CarmoJones extends DDLSystem

    private[this] val worldType: String = "ddlworld"
    @inline private[this] def cworldType: THF.Formula = str2Fun(worldType)
    private[this] val valid: String = "ddlvalid"
    @inline private[this] def cvalid: THF.Formula = str2Fun(valid)


    def apply(): TPTP.Problem = {
      import leo.modules.tptputils.SyntaxTransform.transformProblem
      val problemTHF = transformProblem(TPTP.AnnotatedFormula.FormulaType.THF, problem, addMissingTypeDeclarations = true)
      val formulas = problemTHF.formulas
      val (spec, properFormulas) = splitInput(formulas)
      createState(spec)
      if (ddlSystem == Unknown) throw new EmbeddingException("Embedding not possible as the logic specification did not specify" +
        "the ddl system to be used.")

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

        case THF.ConnectiveTerm(conn) => convertConnective(conn)

        case _ => throw new EmbeddingException(s"Formula unsupported by logic '$name': '${formula.pretty}'")
      }
    }

    private[this] val boxConnective: String = "$$box" // for Avqist and CJ
    private[this] val actualBoxConnective: String = "$$actualBox" // for CJ only
    private[this] val potentialBoxConnective: String = "$$potentialBox" // for CJ only
    private[this] val diaConnective: String = "$$dia" // for Avqist and CJ
    private[this] val actualDiaConnective: String = "$$actualDia" // for CJ only
    private[this] val potentialDiaConnective: String = "$$potentialDia" // for CJ only
    private[this] val obligationConnective: String = "$$obl" // for Avqist and CJ
    private[this] val actualObligationConnective: String = "$$actualObl" // for CJ only
    private[this] val primaryObligationConnective: String = "$$primaryObl" // for CJ only

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
    private[this] val actualbox: String = "ddlboxav"
    private[this] val actualdia: String = "ddldiaav"
    private[this] val potentialbox: String = "ddlboxpv"
    private[this] val potentialdia: String = "ddldiapv"
    private[this] val obligation: String = "ddlobl"
    private[this] val actualobligation: String = "ddloblav"
    private[this] val primaryobligation: String = "ddloblpv"

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
              case `actualBoxConnective` => str2Fun(actualbox)
              case `potentialBoxConnective` => str2Fun(potentialbox)
              case `diaConnective` => str2Fun(dia)
              case `actualDiaConnective` => str2Fun(actualdia)
              case `potentialDiaConnective` => str2Fun(potentialdia)
              case `obligationConnective` => str2Fun(obligation)
              case `actualObligationConnective` => str2Fun(actualobligation)
              case `primaryObligationConnective` => str2Fun(primaryobligation)
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


    private def generateMetaFormulas(): Seq[TPTP.AnnotatedFormula] = {
      import scala.collection.mutable

      val result: mutable.Buffer[TPTP.AnnotatedFormula] = mutable.Buffer.empty
      /////////////////////////////////////////////////////////////
      // First: Introduce world type
      result.append(worldTypeTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Introduce mrel
      result.append(simpleAccessibilityRelationTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define valid
      result.appendAll(validTPTPDef())
      // if carmo jones, then further meta constants:
      if (ddlSystem == CarmoJones) result.appendAll(carmoJonesMetaTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define connectives
      result.appendAll(connectivesTPTPDef())
      /////////////////////////////////////////////////////////////
      // Then: Define modal operators
      ddlSystem match {
        case CarmoJones => result.appendAll(carmoJonesDDLOperatorsTPTPDef())
        case _ => result.appendAll(aqvistDDLOperatorsTPTPDef())
      }
      /////////////////////////////////////////////////////////////
      // Return all
      result.toSeq
    }


    private[this] def worldTypeTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf($worldType, type, $worldType: $$tType).")
    }
    private[this] def simpleAccessibilityRelationTPTPDef(): TPTP.AnnotatedFormula = {
      import leo.modules.input.TPTPParser.annotatedTHF
      annotatedTHF(s"thf(mrel_type, type, mrel: $worldType > $worldType > $$o).")
    }

    private[this] val avset: String = "ddlav"
    private[this] val pvset: String = "ddlpv"
    private[this] val obset: String = "ddlob"

    private[this] def carmoJonesMetaTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${avset}_type, type, $avset: $worldType > $worldType > $$o)."),
        annotatedTHF(s"thf(${pvset}_type, type, $pvset: $worldType > $worldType > $$o)."),
        annotatedTHF(s"thf(${obset}_type, type, $obset: ($worldType > $$o) > ($worldType > $$o) > $$o)."),
        annotatedTHF(s"thf(ddl_av, axiom, ![W:$worldType]: (? [X: $worldType]: ($avset @ W @ X)))."),
        annotatedTHF(s"thf(ddl_pv1, axiom, ![W:$worldType, X:$worldType]: ( ($avset @ W @ X) => ($pvset @ W @ X)))."),
        annotatedTHF(s"thf(ddl_pv2, axiom, ![W:$worldType]: ( ($pvset @ W @ W)))."),
        annotatedTHF(s"thf(ddl_ob1, axiom, ![X:$worldType>$$o]: (~($obset @ X @ (^[Y: $worldType]: ($$false)))))."),
        annotatedTHF(
          s"""thf(ddl_ob2, axiom,
             |  ! [X: $worldType > $$o,Y: $worldType > $$o,Z: $worldType > $$o] :
             |            ( ! [W: $worldType] :
             |                ( ( ( Y @ W ) & ( X @ W ) ) <=> ( ( Z @ W ) & ( X @ W ) ) )
             |           => ( ( $obset @ X @ Y ) <=> ( $obset @ X @ Z ) ) )
             |).""".stripMargin),
        annotatedTHF(
          s"""thf(ddl_ob3, axiom,
             |! [X: $worldType > $$o,BB: ( $worldType > $$o ) > $$o] :
             |            ( ( ! [Z: $worldType > $$o] : ( ( BB @ Z ) => ( $obset @ X @ Z ) )
             |              & ? [Z: $worldType > $$o] :
             |                  ( BB @ Z ) )
             |           => ( ? [Y: $worldType] :
             |                  ( ( ^ [W: $worldType] :
             |                      ! [Z: $worldType > $$o] :
             |                        ( ( BB @ Z )
             |                       => ( Z @ W ) )
             |                    @ Y )
             |                  & ( X @ Y ) )
             |             => ( $obset @ X
             |                @ ^ [W: $worldType] :
             |                  ! [Z: $worldType > $$o] :
             |                    ( ( BB @ Z )
             |                   => ( Z @ W ) ) ) ) )
             |).""".stripMargin),
        annotatedTHF(
          s"""thf(ddl_ob4, axiom,
             |! [X: $worldType > $$o,Y: $worldType > $$o,Z: $worldType > $$o] :
             |           ( ( ! [W: $worldType] :
             |                 ( ( Y @ W )
             |                => ( X @ W ) )
             |             & ( $obset @ X @ Z )
             |             & ? [W: $worldType] :
             |                 ( ( Y @ W )
             |                 & ( Z @ W ) ) )
             |          => ( $obset @ Y
             |             @ ^ [W: $worldType] :
             |                 ( ( ( Z @ W )
             |                   & ~ ( X @ W ) )
             |                 | ( Y @ W ) ) ) )
             |).""".stripMargin),
        annotatedTHF(
          s"""thf(ddl_ob5, axiom,
             |! [X: $worldType > $$o,Y: $worldType > $$o,Z: $worldType > $$o] :
             |            ( ( ! [W: $worldType] :
             |                  ( ( Y @ W )
             |                 => ( X @ W ) )
             |              & ( $obset @ X @ Z )
             |              & ? [W: $worldType] :
             |                  ( ( Y @ W )
             |                  & ( Z @ W ) ) )
             |           => ( $obset @ Y @ Z ) )
             |).""".stripMargin)
      )
    }

    private[this] def validTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${valid}_type, type, $valid: ($worldType > $$o) > $$o)."),
        annotatedTHF(s"thf(${valid}_def, definition, $valid = (^ [Phi: $worldType > $$o]: ![W: $worldType]: (Phi @ W)) ).")
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
    private[this] def aqvistDDLOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${box}_type, type, $box: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${box}_def, definition, ( $box = (^ [Phi:$worldType>$$o, W:$worldType]: ![V:$worldType]: ( Phi @ V ))))."),
        annotatedTHF(s"thf(${dia}_type, type, $dia: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${dia}_def, definition, ( $dia = (^ [Phi:$worldType>$$o, W:$worldType]: ?[V:$worldType]: ( Phi @ V ))))."),
        annotatedTHF(s"thf(${obligation}_type, type, $obligation: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${obligation}_def, definition, ( $obligation = (^ [A:$worldType>$$o, B: $worldType>$$o, X:$worldType]: ![W:$worldType]: ( ((A @ W) & (! [Y:$worldType] : ( (A @ Y) => (mrel @ W @ Y) ))) => (B @ W) )))).")
      )
    }

    private[this] def carmoJonesDDLOperatorsTPTPDef(): Seq[TPTP.AnnotatedFormula] = {
      import leo.modules.input.TPTPParser.annotatedTHF
      Seq(
        annotatedTHF(s"thf(${box}_type, type, $box: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${box}_def, definition, ( $box = (^ [Phi:$worldType>$$o, W:$worldType]: ![V:$worldType]: ( Phi @ V ))))."),
        annotatedTHF(s"thf(${actualbox}_type, type, $actualbox: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${actualbox}_def, definition, ( $actualbox = (^ [Phi:$worldType>$$o, W:$worldType]: ![V:$worldType]: ( ($avset @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(${potentialbox}_type, type, $potentialbox: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${potentialbox}_def, definition, ( $potentialbox = (^ [Phi:$worldType>$$o, W:$worldType]: ![V:$worldType]: ( ($pvset @ W @ V) => (Phi @ V) ))))."),
        annotatedTHF(s"thf(${obligation}_type, type, $obligation: ($worldType>$$o)>($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${obligation}_def, definition, ( $obligation = (^ [A:$worldType>$$o, B: $worldType>$$o, X:$worldType]: ($obset @ A @ B))))."),
        annotatedTHF(s"thf(${actualobligation}_type, type, $actualobligation: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${actualobligation}_def, definition, ( $actualobligation = (^ [A:$worldType>$$o, X:$worldType]: (($obset @ ($avset @ X) @ A) & ( ? [Y:$worldType]: (($avset @ X @ Y) & (~(A @ Y)))) ))))."),
        annotatedTHF(s"thf(${primaryobligation}_type, type, $primaryobligation: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${primaryobligation}_def, definition, ( $primaryobligation = (^ [A:$worldType>$$o, X:$worldType]: (($obset @ ($pvset @ X) @ A) & ( ? [Y:$worldType]: (($pvset @ X @ Y) & (~(A @ Y)))) ))))."),
        annotatedTHF(s"thf(${dia}_type, type, $dia: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${dia}_def, definition, ( $dia = (^ [Phi:$worldType>$$o]: ( $not @ ($box @ ($not @ Phi)) ))))."),
        annotatedTHF(s"thf(${actualdia}_type, type, $actualdia: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${actualdia}_def, definition, ( $actualdia = (^ [Phi:$worldType>$$o]: ( $not @ ($actualbox @ ($not @ Phi)) ))))."),
        annotatedTHF(s"thf(${potentialdia}_type, type, $potentialdia: ($worldType>$$o)>$worldType>$$o )."),
        annotatedTHF(s"thf(${potentialdia}_def, definition, ( $potentialdia = (^ [Phi:$worldType>$$o]: ( $not @ ($potentialbox @ ($not @ Phi)) )))).")
      )
    }

    //////////////////////////////////////////////////////////////////////
    // Logic specification parsing
    //////////////////////////////////////////////////////////////////////

    private[this] def createState(spec: TPTP.AnnotatedFormula): Unit = {
      spec.formula match {
        case THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(`name`, Seq()),THF.Tuple(spec0)))  =>
          spec0 foreach {
            case THF.BinaryFormula(THF.==, THF.FunctionTerm(propertyName, Seq()), rhs) =>
              propertyName match {
                case "$$system" =>
                  rhs match {
                    case THF.FunctionTerm(system, Seq()) =>
                      system match {
                        case "$$aqvistE" => ddlSystem = AqvistE
                        case "$$aqvistF" => ddlSystem = AqvistF
                        case "$$aqvistG" => ddlSystem = AqvistG
                        case "$$carmoJones" => ddlSystem = CarmoJones
                        case _ => throw new EmbeddingException(s"Unknown DDL system value '$system' in logic specification ${spec.pretty}")
                      }
                    case  _ => throw new EmbeddingException(s"Malformed system value '${rhs.pretty}' in logic specification ${spec.pretty}")
                  }
                case _ => throw new EmbeddingException(s"Unknown logic semantics property '$propertyName'")
              }
            case s => throw new EmbeddingException(s"Malformed logic specification entry: ${s.pretty}")
          }
        case _ => throw new EmbeddingException(s"Malformed logic specification entry: ${spec.pretty}")
      }
    }

  }

}
