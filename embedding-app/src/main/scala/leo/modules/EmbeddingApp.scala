package leo.modules

import leo.datastructures.TPTP
import leo.datastructures.TPTP.{AnnotatedFormula, Problem}
import leo.modules.embeddings.{Embedding, EmbeddingException, Library, getLogicFromSpec, getLogicSpecFromProblem}
import leo.modules.embeddings.MalformedLogicSpecificationException
import leo.modules.input.TPTPParser

import scala.io.Source
import java.io.{File, FileNotFoundException, PrintWriter}
import scala.collection.mutable

object EmbeddingApp {
  final val name: String = "embedproblem"
  final val version: String = "1.7.13"

  private[this] var inputFileName = ""
  private[this] var outputFileName: Option[String] = None
  private[this] var logic: Option[String] = None
  private[this] var parameterNames: Set[String] = Set.empty
  private[this] var specs: Map[String, String] = Map.empty
  private[this] var tstpOutput: Boolean = false

  final def main(args: Array[String]): Unit = {
    if (args.contains("--help")) {
      usage(); return
    }
    if (args.contains("--version")) {
      printVersion(); return
    }
    if (args.isEmpty) usage()
    else {
      var infile: Option[Source] = None
      var outfile: Option[PrintWriter] = None
      var error: Option[String] = None

      try {
        parseArgs(args.toSeq)
        // Allocate output file
        outfile = Some(if (outputFileName.isEmpty) new PrintWriter(System.out) else new PrintWriter(new File(outputFileName.get)))
        // Read input
        infile = Some(if (inputFileName == "-") io.Source.stdin else io.Source.fromFile(inputFileName))
        // Create local copy if it is from stdin; since we cannot reset the inputstreamreader afterwards
        val infileCopyAsString = if (inputFileName == "-") {
          val res = infile.get.getLines().mkString("\n")
          infile = Some(io.Source.fromString(res)) // reset infile virtually to stdin input
          Some(res)
        } else None

        // Parse and select embedding
        val parsedInput = TPTPParser.problem(infile.get)
        val maybeLogicSpec = getLogicSpecFromProblem(parsedInput.formulas)
        val maybeGoalLogic = getLogic(maybeLogicSpec)
        val result = maybeGoalLogic match {
          case None => // no goal logic set, return input file as-is
            val sb: mutable.StringBuilder = new mutable.StringBuilder()
            sb.append("% Info: No logic specification given, input problem is returned unchanged. Maybe specify logic with the -l option?\n")
            if (tstpOutput) sb.append(s"% SZS status Success for $inputFileName\n")
            if (tstpOutput) sb.append(s"% SZS output start ListOfFormulae for $inputFileName\n")
            // if not from stdin, we can safely re-read the input file, so we just reset the infile reader
            val copyOfInputLines = if (inputFileName == "-") Seq(infileCopyAsString.get) else infile.get.reset().getLines()
            copyOfInputLines foreach { line => // just print it
              sb.append(line)
              sb.append("\n")
            }
            if (tstpOutput) sb.append(s"% SZS output end ListOfFormulae for $inputFileName\n")
            sb.toString()
          case Some(goalLogic) => // goal logic set, do the embedding steps
            val embeddingFunction = try {
              Library.embeddingTable(goalLogic)
            } catch {
              case _: NoSuchElementException => throw new UnsupportedLogicException(goalLogic)
            }
            // Transform embedding parameters
            val parameters = parameterNames.map { p =>
              try {
                embeddingFunction.embeddingParameter.withName(p)
              } catch {
                case _: NoSuchElementException => throw new UnknownParameterException(p, embeddingFunction.embeddingParameter.values.mkString(","))
              }
            }
            // Do embedding
            // First: Prepend logic specification if none exists.
            val logicSpec = if (maybeLogicSpec.isDefined) maybeLogicSpec.get else embeddingFunction.generateSpecification(specs)
            val problemToBeEmbedded = if (maybeLogicSpec.isDefined) parsedInput else TPTP.Problem(parsedInput.includes, parsedInput.formulas.prepended(logicSpec), Map.empty)
            // Embedding
            val embeddedProblem = embeddingFunction.apply(problemToBeEmbedded, parameters)
            generateResult(embeddedProblem, logicSpec, embeddingFunction)
        }
        // Write result
        outfile.get.print(result)
        outfile.get.flush()
        // Error handling
      } catch {
        case e: EmbeddingException =>
          error = Some(s"An error occurred during embedding: ${e.getMessage}")
        case e: IllegalArgumentException =>
          error = if (e.getMessage == null) Some(e.toString) else Some(e.getMessage)
          if (!tstpOutput) usage()
        case e: UnsupportedLogicException =>
          error = Some(s"Unsupported logic '${e.logic}'. Aborting.")
        case e: UnknownParameterException =>
          error = Some(s"Parameter ${e.parameterName} is unknown. Valid parameters are: ${e.allowedParameters}")
        case e: MalformedLogicSpecificationException =>
          error = Some(s"Logic specification in the input file cannot be interpreted: ${e.spec.pretty}")
        case e: FileNotFoundException =>
          error = Some(s"File cannot be found or is not readable/writable: ${e.getMessage}")
        case e: TPTPParser.TPTPParseException =>
          error = Some(s"Input file could not be parsed, parse error at ${e.line}:${e.offset}: ${e.getMessage}")
        case e: Throwable =>
          error = Some(s"Unexpected error: ${e.getMessage}. This is considered an implementation error, please report this!")
      } finally {
        if (error.nonEmpty) {
          if (tstpOutput) {
            if (outfile.isDefined) {
              outfile.get.println(s"% SZS status Error for $inputFileName : ${error.get}\n")
              outfile.get.flush()
            } else println(s"% SZS status Error for $inputFileName : ${error.get}\n")
          } else {
            if (outfile.isDefined) {
              outfile.get.println(s"Error: ${error.get}")
              outfile.get.flush()
              if (outputFileName.isDefined) {
                if (outputFileName.get != "-") System.err.println(s"Error: ${error.get}")
              }
            } else println(s"Error: ${error.get}")
          }
        }
        try { infile.foreach(_.close())  } catch { case _:Throwable => () }
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
    println(s"usage: $name [-l <logic>] [-p <parameter>] [-s <spec>=<value>] [--tstp] <problem file> [<output file>]")
    println(
      s"""
        | Embed a (non-classical) TPTP problem file into classical higher-order logic (HOL). The logic
        | is chosen based on the logic specification within the input file. If there is no logic specification
        | the input problem is returned unchanged (unless the -l option is given).
        |
        | <problem file> can be either a file name or '-' (without parentheses) for stdin.
        | If <output file> is specified, the result is written to <output file>, otherwise to stdout.
        |
        | Options:
        |  -l <logic>
        |     If <problem file> does not contain a logic specification statement, explicitly set
        |     the input format to <logic>. Ignored if <problem file> contains a logic specification statement.
        |     Supported <logic>s are: ${Library.embeddingTable.keySet.mkString(", ")}
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
        case Seq(f) =>
          args0 = Seq.empty
          inputFileName = f
        case Seq(f, o) =>
          args0 = Seq.empty
          inputFileName = f
          outputFileName = Some(o)
        case _ => throw new IllegalArgumentException("Unrecognized arguments.")
      }
    }
  }

  private[this] class UnknownParameterException(val parameterName: String, val allowedParameters: String) extends RuntimeException
  private[this] class UnsupportedLogicException(val logic: String) extends RuntimeException
}
