package leo
package modules

import java.util.logging.Logger
import datastructures.TPTP
import TPTP.AnnotatedFormula


package object embeddings {
  class EmbeddingException(message: String) extends RuntimeException(message)

  trait Embedding[OptionType] {
    def apply(problem: Seq[AnnotatedFormula], embeddingOptions: Set[OptionType]): Seq[AnnotatedFormula]
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
    import TPTP.THF.{FunctionTerm, :=, BinaryFormula}
    var default: Option[String] = None
    var mapping: Map[String, String] = Map.empty

    tupleElements foreach {
      case FunctionTerm(defaultValue, Seq()) =>
        if (default.isEmpty) {
          default = Some(defaultValue)
        } else throw new EmbeddingException(s"More than one default value for the semantics specification was given. This is considered an error.")
      case BinaryFormula(:=, FunctionTerm(name, Seq()), FunctionTerm(value, Seq())) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name}' given. This is considered an error.")
        else {
          mapping = mapping + (name -> value)
        }
      case e => throw new EmbeddingException(s"Tuple entry of semantics specification could not be read: '${e.pretty}'")
    }
    (default, mapping)
  }

  protected[embeddings] def parseListRHS(rhs: TPTP.THF.Formula): (Seq[String], Map[String, Seq[String]]) = {
    import TPTP.THF.{FunctionTerm, Tuple}
    rhs match {
      case FunctionTerm(f, Seq()) => (Seq(f), Map.empty)
      case Tuple(entries) => parseTupleListRHS(entries)
      case _ => throw new EmbeddingException(s"Right-hand-side of semantics specification could not be read: '${rhs.pretty}'")
    }
  }

  protected[embeddings] def parseTupleListRHS(tupleElements: Seq[TPTP.THF.Formula]): (Seq[String], Map[String, Seq[String]]) = {
    import TPTP.THF.{FunctionTerm, :=, Tuple, BinaryFormula}
    var default: Seq[String] = Seq.empty
    var mapping: Map[String, Seq[String]] = Map.empty

    tupleElements foreach {
      case FunctionTerm(defaultValue, Seq()) =>  default = default :+ defaultValue
      case BinaryFormula(:=, FunctionTerm(name, Seq()), FunctionTerm(value, Seq())) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name}' given. This is considered an error.")
        else {
          mapping = mapping + (name -> Seq(value))
        }
      case bf@BinaryFormula(:=, FunctionTerm(name, Seq()), Tuple(entries)) =>
        if (mapping.isDefinedAt(name)) throw new EmbeddingException(s"More than one value for the identified '${name}' given. This is considered an error.")
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
