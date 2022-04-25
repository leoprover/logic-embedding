package leo
package modules

import leo.datastructures.TPTP
import leo.datastructures.TPTP.AnnotatedFormula

import java.util.logging.Logger


package object embeddings {
  final class EmbeddingException(message: String) extends RuntimeException(message)
  final class MalformedLogicSpecificationException(val spec: TPTP.AnnotatedFormula) extends RuntimeException
  final class UnspecifiedLogicException extends RuntimeException

  final val tptpDefinedNullaryPredicateSymbols: Seq[String] = Seq("$true", "$false")

  final val tptpDefinedUnaryArithmeticPredicateSymbols: Seq[String] = Seq("$is_int", "$is_rat")

  final val tptpDefinedUnaryArithmeticFunctionSymbols: Seq[String] = Seq("$uminus", "$floor", "$ceiling", "$truncate", "$round",
  "$is_int", "$is_rat", "$to_int", "$to_rat", "$to_real")

  final val tptpDefinedBinaryArithmeticPredicateSymbols: Seq[String] = Seq("$less", "$lesseq", "$greater", "$greatereq")

  final val tptpDefinedBinaryArithmeticFunctionSymbols: Seq[String] = Seq("$difference", "$sum", "$product", "$quotient",
    "$quotient_e", "$quotient_t", "$quotient_f", "$remainder_e", "$remainder_t", "$remainder_f")

  final def getLogicSpecFromProblem(formulas: Seq[TPTP.AnnotatedFormula]): Option[TPTP.AnnotatedFormula] = {
    formulas.find(f => f.role == "logic")
  }
  final def getLogicFromSpec(formula: AnnotatedFormula): String = {
    import leo.datastructures.TPTP.{THF,TFF}
    formula match {
      case TPTP.THFAnnotated(_, "logic", THF.Logical(THF.BinaryFormula(THF.==, THF.FunctionTerm(logic, Seq()), _)), _) => logic
      case TPTP.TFFAnnotated(_, "logic", TFF.Logical(TFF.MetaIdentity(TFF.AtomicTerm(logic, Seq()), _)), _) => logic
      case _ => throw new MalformedLogicSpecificationException(formula)
    }
  }

  @inline final def str2Fun(functionName: String): TPTP.THF.Formula = TPTP.THF.FunctionTerm(functionName, Seq.empty)

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
}
