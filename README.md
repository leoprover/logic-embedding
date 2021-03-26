logic-embedding
------
_A tool for embedding non-classical logics into higher-order logic (HOL)_

The tool translates a TPTP problem statement formulated in a non-classical logic 
(using the logic specification format) into monomorphic or polymorphic THF.


## Logics
Currently, only modal logics is supported. More logics will be added soon.

## Usage
```
usage: embedproblem [-l <logic>] [-p <parameter>] [-s <spec>=<value>] <problem file> [<output file>]

 <problem file> can be either a file name or '-' (without parentheses) for stdin.
 If <output file> is specified, the result is written to <output file>, otherwise to stdout.

 Options:
  -l <logic>
     If <problem file> does not contain a logic specification statement, explicitly set
     the input format to <logic>. Ignored, if <problem file> contains a logic specification statement.
     Supported <logic>s are: modal

  -p <parameter>
     Pass transformation parameter <parameter> to the embedding procedure.

  -s <spec>=<value>
     If <problem file> does not contain a logic specification statement, explicitly set
     semantics of <spec> to <value>. In this case, -l needs to be provided.
     Ignored, if <problem file> contains a logic specification statement.

  --version
     Prints the version number of the executable and terminates.

  --help
     Prints this description and terminates.
```


## Notes
The modal logic embedding is a modified and consolidated re-implementation of Tobias Gleißner's embedding tool at the leoprover/embed_modal repository.
This version makes use of the `scala-tptp-parser` library from leoprover/scala-tptp-parser that is much faster, in particular for larger input problems.
