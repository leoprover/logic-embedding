package leo.modules

import leo.datastructures.TPTP
import leo.datastructures.TPTP.{AnnotatedFormula, Problem}
import leo.modules.embeddings.{Embedding, EmbeddingException, EmbeddingN, Library, MalformedLogicSpecificationException, UnsupportedFragmentException, getLogicFromSpec, getLogicSpecFromProblem}
import leo.modules.input.TPTPParser

import java.io.{File, FileNotFoundException, PrintWriter}
import java.nio.file.Path
import scala.collection.mutable

object EmbeddingApp {
  final val name: String = "embedproblem"
  final val version: String = "1.9.5"

  private[this] var inputFileName = ""
  private[this] var outputFileName: Option[String] = None
  private[this] var logic: Option[String] = None
  private[this] var parameterNames: Set[String] = Set.empty
  private[this] var specs: Map[String, String] = Map.empty
  private[this] var tstpOutput: Boolean = false
  private[this] val tptpHomeDirectory: Option[String] = sys.env.get("TPTP")

  final def main(args: Array[String]): Unit = {
    if (args.contains("--help")) {
      usage(); return
    }
    if (args.contains("--version")) {
      printVersion(); return
    }
    if (args.isEmpty) usage()
    else {
      var infile: Option[Path] = None
      var outfile: Option[PrintWriter] = None
      var error: Option[(String, String)] = None // Tuple (SZS value, message)

      try {
        parseArgs(args.toSeq)
        infile = Some(if (inputFileName == "-") Path.of("-") else Path.of(inputFileName).toAbsolutePath)
        // Parse and select embedding
        val parsedInput = leo.modules.tptputils.parseTPTPFileWithIncludes(infile.get, tptpHomeDirectory)
        val maybeLogicSpec = getLogicSpecFromProblem(parsedInput.formulas)
        val maybeGoalLogic = getLogic(maybeLogicSpec)
        // result is not a sequence, we need to print every entry individually
        val results: Seq[String] = maybeGoalLogic match {
          case None => // no goal logic set, return input file as-is
            val sb: mutable.StringBuilder = new mutable.StringBuilder()
            sb.append("% Info: No logic specification given, input problem is returned unchanged. Maybe specify logic with the -l option?\n")
            if (tstpOutput) sb.append(s"% SZS status Success for $inputFileName\n")
            if (tstpOutput) sb.append(s"% SZS output start ListOfFormulae for $inputFileName\n")
            sb.append(leo.modules.tptputils.tptpProblemToString(parsedInput))
            sb.append("\n")
            if (tstpOutput) sb.append(s"% SZS output end ListOfFormulae for $inputFileName\n")
            Seq(sb.toString())
          case Some(goalLogic) => // goal logic set, do the embedding steps
            val embeddingFunction = try {
              Library.embeddingTable(goalLogic)
            } catch {
              case _: NoSuchElementException => throw new UnsupportedLogicException(goalLogic)
            }
            // Do embedding
            // First: Prepend logic specification if none exists.
            val logicSpec = if (maybeLogicSpec.isDefined) maybeLogicSpec.get else embeddingFunction.generateSpecification(specs)
            val problemToBeEmbedded = if (maybeLogicSpec.isDefined) parsedInput else TPTP.Problem(parsedInput.includes, parsedInput.formulas.prepended(logicSpec), Map.empty)
            // Embedding
            embeddingFunction match {
              case embeddingFunctionN: EmbeddingN =>
                // Transform embedding parameters (explicitly repeated because of subtype incompability. Ugly, but small scope.)
                //noinspection DuplicatedCode
                val parameters = parameterNames.map { p =>
                  try {
                    embeddingFunctionN.embeddingParameter.withName(p)
                  } catch {
                    case _: NoSuchElementException => throw new UnknownParameterException(p, embeddingFunction.embeddingParameter.values.mkString(","))
                  }
                }
                val embeddedProblems = embeddingFunctionN.applyN(problemToBeEmbedded, parameters)
                embeddedProblems.map(eb => generateResult(eb, logicSpec, embeddingFunction))
              case _ =>
                // Transform embedding parameters
                //noinspection DuplicatedCode
                val parameters = parameterNames.map { p =>
                  try {
                    embeddingFunction.embeddingParameter.withName(p)
                  } catch {
                    case _: NoSuchElementException => throw new UnknownParameterException(p, embeddingFunction.embeddingParameter.values.mkString(","))
                  }
                }
                val embeddedProblem = embeddingFunction.apply(problemToBeEmbedded, parameters)
                Seq(generateResult(embeddedProblem, logicSpec, embeddingFunction))
            }
        }
        // Allocate output files and write result
        if (results.size == 1) {
          outfile = Some(if (outputFileName.isEmpty) new PrintWriter(System.out) else new PrintWriter(new File(s"${outputFileName.get}")))
          // Write result
          outfile.get.print(results.head)
          outfile.get.flush()
          // if it is stdout, dont close yet (will be closed anyway in finally clause below)
          if (outputFileName.nonEmpty) outfile.get.close()
        } else {
          for (result <- results.zipWithIndex) {
            outfile = Some(if (outputFileName.isEmpty) new PrintWriter(System.out) else new PrintWriter(new File(s"${outputFileName.get}.${result._2}")))
            // Write result
            outfile.get.print(result._1)
            outfile.get.flush()
            // if it is stdout, dont close yet (will be closed anyway in finally clause below)
            if (outputFileName.nonEmpty) outfile.get.close()
          }
        }
      // Error handling
      } catch {
        case e: EmbeddingException =>
          error = Some("Error", s"An error occurred during embedding: ${e.getMessage}")
        case e: UnsupportedFragmentException =>
          error = Some("Inappropriate", s"The input file contains unsupported language features: ${e.getMessage}")
        case e: IllegalArgumentException =>
          error = if (e.getMessage == null) Some("UsageError", e.toString) else Some("UsageError", e.getMessage)
          if (!tstpOutput) usage()
        case e: UnsupportedLogicException =>
          error = Some("Inappropriate", s"Unsupported logic '${e.logic}'. Aborting.")
        case e: UnknownParameterException =>
          error = Some("UsageError", s"Parameter ${e.parameterName} is unknown. Valid parameters are: ${e.allowedParameters}")
        case e: MalformedLogicSpecificationException =>
          error = Some("Unsemantic", s"Logic specification in the input file cannot be interpreted: ${e.spec.pretty}")
        case e: FileNotFoundException =>
          error = Some("InputError", s"File cannot be found or is not readable/writable: ${e.getMessage}")
        case e: TPTPParser.TPTPParseException =>
          error = Some("SyntaxError", s"Input file could not be parsed, parse error at ${e.line}:${e.offset}: ${e.getMessage}")
        case e: Throwable =>
          error = Some("Error", s"Unexpected error: ${e.getMessage}. This is considered an implementation error, please report this!")
          System.err.println(s"Exception: ${e.toString}")
          e.printStackTrace()
      } finally {
        if (error.nonEmpty) {
          val (szsStatus, errorMessage) = error.get
          if (tstpOutput) {
            if (outfile.isDefined) {
              outfile.get.println(s"% SZS status $szsStatus for $inputFileName : $errorMessage\n")
              outfile.get.flush()
            } else println(s"% SZS status $szsStatus for $inputFileName : $errorMessage\n")
          } else {
            if (outfile.isDefined) {
              outfile.get.println(s"$szsStatus: $errorMessage")
              outfile.get.flush()
              if (outputFileName.isDefined) {
                if (outputFileName.get != "-") System.err.println(s"$szsStatus: $errorMessage")
              }
            } else println(s"$szsStatus: $errorMessage")
          }
        }
        try { outfile.foreach(_.close()) } catch { case _:Throwable => () }
        if (error.nonEmpty) System.exit(1)
      }
    }
  }



  private[this] final def generateResult(problem: Problem, logicSpec: AnnotatedFormula, embedding: Embedding): String = {
    import java.util.Calendar

    val sb: mutable.StringBuilder = new mutable.StringBuilder()
    if (tstpOutput) sb.append(s"% SZS status Success for $inputFileName\n")
    sb.append(s"%%% This output was generated by $name, version $version (library version ${Library.version}).\n")
    sb.append(s"%%% Generated on ${Calendar.getInstance().getTime.toString}\n")
    sb.append(s"%%% using '${embedding.name}' embedding, version ${embedding.version}.\n")
    sb.append(s"%%% Logic specification used:\n")
    sb.append(s"%%% ${logicSpec.pretty}\n")
    if (parameterNames.nonEmpty) {
      sb.append(s"%%% Transformation parameters: ${parameterNames.mkString(",")}\n")
    }
    sb.append("\n")
    if (tstpOutput) sb.append(s"% SZS output start ListOfTHF for $inputFileName\n")
    sb.append(problem.pretty)
    sb.append("\n")
    if (tstpOutput) sb.append(s"% SZS output end ListOfTHF for $inputFileName\n")
    sb.toString()
  }

  private[this] final def getLogic(maybeSpec: Option[TPTP.AnnotatedFormula]): Option[String] = maybeSpec match {
      case Some(value) => Some(getLogicFromSpec(value))
      case None if logic.isDefined => Some(logic.get)
      case None => None
    }

  private[this] final def printVersion(): Unit = {
    println(s"$name $version")
  }

  private[this] final def usage(): Unit = {
    println(s"usage: $name [options] <problem file>")
    println(
      s"""
        | Embed a (non-classical) TPTP problem file into classical higher-order logic (HOL).
        | The logic is chosen based on the logic specification within the input file. If there
        | is no logic specification the input problem is returned unchanged
        | (unless the -l option is given, see below).
        |
        | <problem file> can be either a file name or '-' (without parentheses) for stdin.
        | If <output file> is specified (using --output, see below), the result is written to
        | <output file>, otherwise to stdout.
        |
        | Options:
        |  -l <logic>
        |     If <problem file> does not contain a logic specification statement, -l <logic>
        |     explicitly sets the input logic to <logic>.
        |     This option is ignored if <problem file> contains a logic specification statement.
        |     Supported <logic>s are:
        |     ${Library.embeddingTable.keySet.mkString(", ")}
        |
        |  -p <parameter>
        |     Pass transformation parameter <parameter> to the embedding procedure.
        |
        |  -s <spec>=<value>
        |     If <problem file> does not contain a logic specification statement, explicitly set
        |     semantics of <spec> to <value>. In this case, -l needs to be provided.
        |     Ignored, if <problem file> contains a logic specification statement.
        |
        |  --tstp
        |     Enable TSTP-compatible output: The output in <output file> (or stdout) will
        |     start with a SZS status value and the output will be wrapped within
        |     SZS BEGIN and SZS END block delimiters. Disabled by default.
        |
        |  --output <output file>
        |     Do not write the result to stdout, but to <output file>.
        |     This will overwrite <output file> if it already exists.
        |     If the embedding potentially outputs multiple results, the output files
        |     are named <output file>.0, <output file>.1, <output file>.2, etc.
        |
        |  --version
        |     Prints the version number of the executable and terminates.
        |
        |  --help
        |     Prints this description and terminates.
        |""".stripMargin)
  }

  private[this] final def parseArgs(args: Seq[String]): Unit = {
    var args0 = args
    while (args0.nonEmpty) {
      args0 match {
        case Seq("-l", l, rest@_*) =>
          args0 = rest
          logic = Some(l)
        case Seq("-p", p, rest@_*) =>
          args0 = rest
          parameterNames = parameterNames + p
        case Seq("-s", eq, rest@_*) =>
          args0 = rest
          eq.split("=", 2).toSeq match {
            case Seq(l, r) => specs = specs + (l -> r)
            case _ => throw new IllegalArgumentException(s"Malformed argument to -s option: '$eq'")
          }
        case Seq("--tstp", rest@_*) =>
          args0 = rest
          tstpOutput = true
        case Seq("--output", o, rest@_*) =>
          args0 = rest
          outputFileName = Some(o)
        case Seq(f, rest@_*) if inputFileName.isEmpty =>
          args0 = rest
          inputFileName = f
        case _ => throw new IllegalArgumentException(s"Unrecognized or superfluous options/arguments: ${args0.mkString(",")}.")
      }
    }
  }

  private[this] class UnknownParameterException(val parameterName: String, val allowedParameters: String) extends RuntimeException
  private[this] class UnsupportedLogicException(val logic: String) extends RuntimeException
}
