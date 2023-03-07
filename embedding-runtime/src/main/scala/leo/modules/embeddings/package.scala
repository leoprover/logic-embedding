package leo
package modules

import leo.datastructures.TPTP
import leo.datastructures.TPTP.{AnnotatedFormula, TFF, TFFAnnotated, THF, THFAnnotated}

import java.util.logging.Logger
import scala.annotation.tailrec


package object embeddings {
  final class EmbeddingException(message: String) extends RuntimeException(message)
  final class MalformedLogicSpecificationException(val spec: TPTP.AnnotatedFormula) extends RuntimeException


  final val tptpDefinedNullaryPredicateSymbols: Seq[String] = Seq("$true", "$false")
  final val tptpDefinedUnaryArithmeticPredicateSymbols: Seq[String] = Seq("$is_int", "$is_rat")
  final val tptpDefinedBinaryArithmeticPredicateSymbols: Seq[String] = Seq("$less", "$lesseq", "$greater", "$greatereq")
  final val tptpDefinedPredicateSymbols: Seq[String] = tptpDefinedNullaryPredicateSymbols ++ tptpDefinedUnaryArithmeticPredicateSymbols ++ tptpDefinedBinaryArithmeticPredicateSymbols

  final val tptpDefinedUnaryArithmeticFunctionSymbols: Seq[String] = Seq("$uminus", "$floor", "$ceiling", "$truncate", "$round",
  "$is_int", "$is_rat", "$to_int", "$to_rat", "$to_real")
  final val tptpDefinedBinaryArithmeticFunctionSymbols: Seq[String] = Seq("$difference", "$sum", "$product", "$quotient",
    "$quotient_e", "$quotient_t", "$quotient_f", "$remainder_e", "$remainder_t", "$remainder_f")
  final val tptpDefinedFunctionSymbols: Seq[String] = tptpDefinedUnaryArithmeticFunctionSymbols ++ tptpDefinedBinaryArithmeticFunctionSymbols

  final def getLogicSpecFromProblem(formulas: Seq[TPTP.AnnotatedFormula]): Option[TPTP.AnnotatedFormula] = {
    formulas.find(f => f.role == "logic")
  }
  final def getLogicFromSpec(formula: AnnotatedFormula): String = {
    import leo.datastructures.TPTP.{THF,TFF}
    formula match {
      case TPTP.THFAnnotated(_, "logic", THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(logic, Seq()), _)), _) => logic
      case TPTP.THFAnnotated(_, "logic", THF.Logical(THF.FunctionTerm(logic, Seq())), _) => logic
      case TPTP.TFFAnnotated(_, "logic", TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(logic, Seq()), _)), _) => logic
      case TPTP.TFFAnnotated(_, "logic", TFF.Logical(TFF.AtomicFormula(logic, Seq())), _) => logic
      case _ => throw new MalformedLogicSpecificationException(formula)
    }
  }

  @inline final def str2Fun(functionName: String): TPTP.THF.Formula = TPTP.THF.FunctionTerm(functionName, Seq.empty)

  final def generateFreshTPTPVariableName(startName: String, disallowedNames: Set[String]): String = {
    if (disallowedNames.contains(startName)) {
      var counter: Int = 0
      while (disallowedNames.contains(s"$startName$counter")) {
        counter = counter + 1
      }
      s"$startName$counter"
    } else startName
  }

  final def unescapeTPTPName(name: String): String = {
    if (name.startsWith("'") && name.endsWith("'")) {
      name.tail.init
    } else name
  }

  final def escapeName(name: String): String = {
    val integerRegex = "^[+-]?[\\d]+$"
    if (name.matches(integerRegex)) name else escapeAtomicWord(name)
  }
  final def escapeAtomicWord(word: String): String = {
    val simpleLowerWordRegex = "^[a-z][a-zA-Z\\d_]*$"
    if (word.matches(simpleLowerWordRegex)) word
    else s"'${word.replace("\\", "\\\\").replace("'", "\\'")}'"
  }

  final def encodeDollarName(str: String): String = str.replaceAll("\\$", "d")
  final def serializeType(typ: TPTP.THF.Type): String = {
    import TPTP.THF._

    typ match {
      case FunctionTerm(f, Seq()) => encodeDollarName(f)
      case FunctionTerm(f, args) =>
        val encodedF = encodeDollarName(f)
        s"$encodedF${args.map(serializeType).mkString("__l__", "_", "__r__")}"
      case BinaryFormula(FunTyConstructor, left, right) =>
        s"fun_l__${serializeType(left)}_${serializeType(right)}__r_"
      case BinaryFormula(SumTyConstructor, left, right) =>
        s"sum_l__${serializeType(left)}_${serializeType(right)}__r_"
      case BinaryFormula(ProductTyConstructor, left, right) =>
        s"prod_l__${serializeType(left)}_${serializeType(right)}__r_"
      case _ => throw new IllegalArgumentException()
    }

  }
  @tailrec
  final def goalType(typ: THF.Type): THF.Type = {
    typ match {
      case THF.BinaryFormula(THF.FunTyConstructor, _, right) => goalType(right)
      case _ => typ
    }
  }

  type THFLogicSpec = THFAnnotated
  type THFSortDecl = THFAnnotated
  type THFTypeDecl = THFAnnotated
  type THFDefDecl = THFAnnotated
  type THFRemainingFormulas = THFAnnotated
  protected[embeddings] final def splitTHFInputByDifferentKindOfFormulas(input: Seq[AnnotatedFormula]):
  (THFLogicSpec, Seq[THFSortDecl], Seq[THFTypeDecl], Seq[THFDefDecl], Seq[THFRemainingFormulas]) = {
    import collection.mutable
    val logicSpec: mutable.Buffer[THFLogicSpec] = mutable.Buffer.empty
    val sortDecls: mutable.Buffer[THFSortDecl] = mutable.Buffer.empty
    val typeDecls: mutable.Buffer[THFTypeDecl] = mutable.Buffer.empty
    val defDecls: mutable.Buffer[THFDefDecl] = mutable.Buffer.empty
    val remainingFormulas: mutable.Buffer[THFRemainingFormulas] = mutable.Buffer.empty

    input.foreach {
      case f@THFAnnotated(_, role, formula, _) => role match {
        case "logic" => logicSpec.append(f)
        case "type" => formula match {
          case THF.Typing(_, typ) => typ match {
            case THF.FunctionTerm("$tType", Seq()) => sortDecls.append(f)
            case _ => typeDecls.append(f)
          }
          case _ => throw new EmbeddingException(s"Malformed type definition in formula '${f.name}', aborting.")
        }
        case "definition" => defDecls.append(f)
        case _ => remainingFormulas.append(f)
      }
      case f => throw new EmbeddingException(s"THF formula expected but ${f.formulaType.toString} formula given. Aborting.")
    }

    if (logicSpec.isEmpty) throw new EmbeddingException("No logic specification given. Aborting.")
    else {
      val spec = if (logicSpec.size > 1) {
        Logger.getGlobal.warning(s"More than one logic specification given; only using the first one ('${logicSpec.head.name}'), " +
          s"the remaining ones are ignored.")
        logicSpec.head
      } else logicSpec.head
      (spec, sortDecls.toSeq, typeDecls.toSeq, defDecls.toSeq, remainingFormulas.toSeq)
    }

  }


  type LogicSpec = AnnotatedFormula
  type SortDecl = AnnotatedFormula
  type TypeDecl = AnnotatedFormula
  type DefDecl = AnnotatedFormula
  type RemainingFormulas = AnnotatedFormula
  protected[embeddings] final def splitInputByDifferentKindOfFormulas(input: Seq[AnnotatedFormula]):
  (LogicSpec, Seq[SortDecl], Seq[TypeDecl], Seq[DefDecl], Seq[RemainingFormulas]) = {
    import collection.mutable
    val logicSpec: mutable.Buffer[LogicSpec] = mutable.Buffer.empty
    val sortDecls: mutable.Buffer[SortDecl] = mutable.Buffer.empty
    val typeDecls: mutable.Buffer[TypeDecl] = mutable.Buffer.empty
    val defDecls: mutable.Buffer[DefDecl] = mutable.Buffer.empty
    val remainingFormulas: mutable.Buffer[RemainingFormulas] = mutable.Buffer.empty

    input.foreach { f =>
      f.role match {
        case "logic" => logicSpec.append(f)
        case "type" => f match {
          case TPTP.THFAnnotated(_, _, formula, _) => formula match {
            case THF.Typing(_, typ) => typ match {
              case THF.FunctionTerm("$tType", Seq()) => sortDecls.append(f)
              case _ => typeDecls.append(f)
            }
            case _ => throw new EmbeddingException(s"Malformed type definition in formula '${f.name}', aborting.")
          }
          case _ => throw new EmbeddingException(s"Only embedding of THF files supported. Aborting")
        }
        case "definition" => defDecls.append(f)
        case _ => remainingFormulas.append(f)
      }
    }

    if (logicSpec.isEmpty) throw new EmbeddingException("No logic specification given. Aborting.")
    else {
      val spec = if (logicSpec.size > 1) {
        Logger.getGlobal.warning(s"More than one logic specification given; only using the first one ('${logicSpec.head.name}'), " +
          s"the remaining ones are ignored.")
        logicSpec.head
      } else logicSpec.head
      (spec, sortDecls.toSeq, typeDecls.toSeq, defDecls.toSeq, remainingFormulas.toSeq)
    }
  }

  final def generateTHFSpecification(logicName: String, parameter: Seq[String], specs: Map[String, String]): TPTP.THFAnnotated = {
    import collection.mutable
    val entries: mutable.Buffer[THF.Formula] = mutable.Buffer.empty
    parameter.foreach { param =>
      if (specs.isDefinedAt(param))
        entries.append(THF.BinaryFormula(THF.==, THF.FunctionTerm(param, Seq.empty), THF.FunctionTerm(specs(param), Seq.empty)))
    }
    if (entries.isEmpty)
      THFAnnotated("generated_spec", "logic", THF.Logical(THF.FunctionTerm(logicName, Seq.empty)), None)
    else
      THFAnnotated("generated_spec", "logic", THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(logicName, Seq.empty), THF.Tuple(entries.toSeq))), None)
  }

  /////////// TFF specific split
  protected[embeddings] final def splitTFFInput(input: Seq[AnnotatedFormula]): (TFFAnnotated, Seq[TFFAnnotated]) = {
    import collection.mutable
    val logicSpecs: mutable.Buffer[TFFAnnotated] = mutable.Buffer.empty
    val otherFormulas: mutable.Buffer[TFFAnnotated] = mutable.Buffer.empty

    input.foreach {
      case f@TFFAnnotated(_, role, _, _) => role match {
        case "logic" => logicSpecs.append(f)
        case _ => otherFormulas.append(f)
      }
      case f => throw new EmbeddingException(s"TFF formula expected but ${f.formulaType.toString} formula given. Aborting.")
    }

    if (logicSpecs.isEmpty) throw new EmbeddingException("No logic specification given. Aborting.")
    else {
      val spec = if (logicSpecs.size > 1) {
        Logger.getGlobal.warning(s"More than one logic specification given; only using the first one ('${logicSpecs.head.name}'), " +
          s"the remaining ones are ignored.")
        logicSpecs.head
      } else logicSpecs.head
      (spec, otherFormulas.toSeq)
    }
  }

  type TFFLogicSpec = TFFAnnotated
  type TFFSortDecl = TFFAnnotated
  type TFFTypeDecl = TFFAnnotated
  type TFFDefDecl = TFFAnnotated
  type TFFRemainingFormulas = TFFAnnotated
  protected[embeddings] final def splitTFFInputByDifferentKindOfFormulas(input: Seq[AnnotatedFormula]):
  (TFFLogicSpec, Seq[TFFSortDecl], Seq[TFFTypeDecl], Seq[TFFDefDecl], Seq[TFFRemainingFormulas]) = {
    import collection.mutable
    val logicSpec: mutable.Buffer[TFFLogicSpec] = mutable.Buffer.empty
    val sortDecls: mutable.Buffer[TFFSortDecl] = mutable.Buffer.empty
    val typeDecls: mutable.Buffer[TFFTypeDecl] = mutable.Buffer.empty
    val defDecls: mutable.Buffer[TFFDefDecl] = mutable.Buffer.empty
    val remainingFormulas: mutable.Buffer[TFFRemainingFormulas] = mutable.Buffer.empty

    input.foreach {
      case f@TFFAnnotated(_, role, formula, _) => role match {
        case "logic" => logicSpec.append(f)
        case "type" => formula match {
          case TFF.Typing(_, typ) => typ match {
            case TFF.AtomicType("$tType", Seq()) => sortDecls.append(f)
            case _ => typeDecls.append(f)
          }
          case _ => throw new EmbeddingException(s"Malformed type definition in formula '${f.name}', aborting.")
        }
        case "definition" => defDecls.append(f)
        case _ => remainingFormulas.append(f)
      }
      case f => throw new EmbeddingException(s"TFF formula expected but ${f.formulaType.toString} formula given. Aborting.")
    }

    if (logicSpec.isEmpty) throw new EmbeddingException("No logic specification given. Aborting.")
    else {
      val spec = if (logicSpec.size > 1) {
        Logger.getGlobal.warning(s"More than one logic specification given; only using the first one ('${logicSpec.head.name}'), " +
          s"the remaining ones are ignored.")
        logicSpec.head
      } else logicSpec.head
      (spec, sortDecls.toSeq, typeDecls.toSeq, defDecls.toSeq, remainingFormulas.toSeq)
    }
  }

  final def generateTFFSpecification(logicName: String, parameter: Seq[String], specs: Map[String, String]): TPTP.TFFAnnotated = {
    import collection.mutable
    val entries: mutable.Buffer[TFF.Term] = mutable.Buffer.empty
    parameter.foreach { param =>
      if (specs.isDefinedAt(param)) {
        entries.append(TFF.FormulaTerm(TFF.MetaIdentity(TFF.AtomicTerm(param, Seq.empty),
                                                        TFF.AtomicTerm(specs(param), Seq.empty))))
      }
    }
    if (entries.isEmpty)
      TFFAnnotated("generated_spec", "logic", TFF.Logical(TFF.AtomicFormula(logicName, Seq.empty)), None)
    else
      TFFAnnotated("generated_spec", "logic", TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(logicName, Seq.empty), TFF.Tuple(entries.toSeq))), None)
  }

  protected[embeddings] final def splitInput(input: Seq[AnnotatedFormula]): (AnnotatedFormula, Seq[AnnotatedFormula]) = {
    val (logicSpecifications, remainingFormulas) = input.partition(_.role == "logic")
    if (logicSpecifications.isEmpty) throw new EmbeddingException("No logic specification given. Aborting.")
    else {
      val spec = if (logicSpecifications.size > 1) {
        Logger.getGlobal.warning(s"More than one logic specification given; only using the first one ('${logicSpecifications.head.name}'), " +
          s"the remaining ones are ignored.")
        logicSpecifications.head
      } else logicSpecifications.head
      (spec, remainingFormulas)
    }
  }

  protected[embeddings] def parseRHS(rhs: TPTP.THF.Formula): (Option[String], Map[String, String]) = {
    import TPTP.THF.{FunctionTerm, Tuple}
    rhs match {
      case FunctionTerm(f, Seq()) => (Some(f), Map.empty)
      case Tuple(entries) => parseTupleRHS(entries)
      case _ => throw new EmbeddingException(s"Right-hand-side of semantics specification could not be read: '${rhs.pretty}'")
    }
  }

  protected[embeddings] def parseTupleRHS(tupleElements: Seq[TPTP.THF.Formula]): (Option[String], Map[String, String]) = {
    import TPTP.THF.{BinaryFormula, FunctionTerm}
    var default: Option[String] = None
    var mapping: Map[String, String] = Map.empty

    tupleElements foreach {
      case FunctionTerm(defaultValue, Seq()) =>
        if (default.isEmpty) {
          default = Some(defaultValue)
        } else throw new EmbeddingException(s"More than one default value for the semantics specification was given. This is considered an error.")
      case BinaryFormula(TPTP.THF.==, FunctionTerm(name, Seq()), FunctionTerm(value, Seq())) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '$name' given. This is considered an error.")
        else {
          mapping = mapping + (name -> value)
        }
      case e => throw new EmbeddingException(s"Tuple entry of semantics specification could not be read: '${e.pretty}'")
    }
    (default, mapping)
  }

  protected[embeddings] def parseListRHSNew(rhs: TPTP.THF.Formula): (Seq[TPTP.THF.Formula], Map[TPTP.THF.Formula, Seq[TPTP.THF.Formula]]) = {
    import TPTP.THF.Tuple
    rhs match {
      case Tuple(entries) if entries.nonEmpty => parseTupleListRHSNew(entries)
      case _ => (Seq(rhs), Map.empty)
    }
  }

  protected[embeddings] def parseListRHS(rhs: TPTP.THF.Formula): (Seq[String], Map[TPTP.THF.Formula, Seq[String]]) = {
    import TPTP.THF.{FunctionTerm, Tuple}
    rhs match {
      case FunctionTerm(f, Seq()) => (Seq(f), Map.empty)
      case Tuple(entries) if entries.nonEmpty => parseTupleListRHS(entries)
      case _ => throw new EmbeddingException(s"Right-hand-side of semantics specification could not be read: '${rhs.pretty}'")
    }
  }

  protected[embeddings] def parseTupleListRHS(tupleElements: Seq[TPTP.THF.Formula]): (Seq[String], Map[TPTP.THF.Formula, Seq[String]]) = {
    import TPTP.THF.{BinaryFormula, FunctionTerm, Tuple}
    var default: Seq[String] = Seq.empty
    var mapping: Map[TPTP.THF.Formula, Seq[String]] = Map.empty

    tupleElements foreach {
      case FunctionTerm(defaultValue, Seq()) =>  default = default :+ defaultValue
      case BinaryFormula(TPTP.THF.==, name, FunctionTerm(value, Seq())) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name.pretty}' given. This is considered an error.")
        else {
          mapping = mapping + (name -> Seq(value))
        }
      case bf@BinaryFormula(TPTP.THF.==, name, Tuple(entries)) if entries.nonEmpty =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name.pretty}' given. This is considered an error.")
        else {
          val (convertedEntries, convertedEntriesMap) = parseTupleListRHS(entries)
          if (convertedEntriesMap.isEmpty) {
            mapping = mapping + (name -> convertedEntries)
          } else {
            throw new EmbeddingException(s"Could not read semantic specification '${bf.pretty}'.")
          }
        }

      case e => throw new EmbeddingException(s"Tuple entry of semantics specification could not be read: '${e.pretty}'")
    }
    (default, mapping)
  }


  protected[embeddings] def parseTupleListRHSNew(tupleElements: Seq[TPTP.THF.Formula]): (Seq[TPTP.THF.Formula], Map[TPTP.THF.Formula, Seq[TPTP.THF.Formula]]) = {
    import TPTP.THF.{BinaryFormula, Tuple}
    var default: Seq[TPTP.THF.Formula] = Seq.empty
    var mapping: Map[TPTP.THF.Formula, Seq[TPTP.THF.Formula]] = Map.empty

    tupleElements foreach {
      case bf@BinaryFormula(TPTP.THF.==, name, Tuple(entries)) if entries.nonEmpty =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name.pretty}' given. This is considered an error.")
        else {
          val (convertedEntries, convertedEntriesMap) = parseTupleListRHSNew(entries)
          if (convertedEntriesMap.isEmpty) {
            mapping = mapping + (name -> convertedEntries)
          } else {
            throw new EmbeddingException(s"Could not read semantic specification '${bf.pretty}'.")
          }
        }
      case BinaryFormula(TPTP.THF.==, name, rhs) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name.pretty}' given. This is considered an error.")
        else {
          mapping = mapping + (name -> Seq(rhs))
        }
      case e => default = default :+ e
    }
    (default, mapping)
  }

  final def generateExtraComments(warnings: Seq[String],
                                  maybeFirstFormula: Option[AnnotatedFormula],
                                  maybeSortFormula: Option[AnnotatedFormula],
                                  maybeMetaPreFormula: Option[AnnotatedFormula],
                                  maybeTypeFormula: Option[AnnotatedFormula],
                                  maybeMetaPostFormula: Option[AnnotatedFormula],
                                  maybeDefinitionFormula: Option[AnnotatedFormula],
                                  maybeRestFormula: Option[AnnotatedFormula]): Map[String, Seq[TPTP.Comment]] = {
    var commentMap: Map[String, Seq[TPTP.Comment]] = Map.empty

    // maybe add comments about warnings etc. in comments. If so, add them to very first formula in output.
    if (warnings.nonEmpty) {
      maybeFirstFormula match {
        case Some(formula) => commentMap = commentMap + (formula.name -> warnings.map(TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, _)))
        case None =>
      }
    }
    maybeSortFormula match {
      case Some(formula) =>
        val sortBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% User types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%")
        ))
        commentMap = mergeMaps(commentMap, sortBlockComment)
      case None =>
    }
    maybeMetaPreFormula match {
      case Some(formula) =>
        val metaPreBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% Meta-logical definitions of the embedding %%")
        ))
        commentMap = mergeMaps(commentMap, metaPreBlockComment)
      case None =>
    }
    maybeTypeFormula match {
      case Some(formula) =>
        val typeBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% Converted user type declarations %%%%%%%%%%%")
        ))
        commentMap = mergeMaps(commentMap, typeBlockComment)
      case None =>
    }
    maybeMetaPostFormula match {
      case Some(formula) =>
        val metaPostBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% Additional meta-logical definitions %%%%%%%%")
        ))
        commentMap = mergeMaps(commentMap, metaPostBlockComment)
      case None =>
    }
    maybeDefinitionFormula match {
      case Some(formula) =>
        val definitionBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% Converted user definitions %%%%%%%%%%%%%%%%%")
        ))
        commentMap = mergeMaps(commentMap, definitionBlockComment)
      case None =>
    }
    maybeRestFormula match {
      case Some(formula) =>
        val restBlockComment = Map(formula.name -> Seq(
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"),
          TPTP.Comment(TPTP.Comment.CommentFormat.LINE, TPTP.Comment.CommentType.NORMAL, "%% Converted problem %%%%%%%%%%%%%%%%%%%%%%%%%%")
        ))
        commentMap = mergeMaps(commentMap, restBlockComment)
      case None =>
    }
    commentMap
  }

  private[this] def mergeMaps[A, B](left: Map[A, Seq[B]], right: Map[A, Seq[B]]): Map[A, Seq[B]] = {
    var result: Map[A, Seq[B]] = left
    right.foreach { case (key, values) =>
      val existingValues = result.getOrElse(key, Seq.empty)
      result = result + (key -> (existingValues ++ values))
    }
    result
  }
}
