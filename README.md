logic-embedding
------
_A tool for embedding non-classical logics into higher-order logic (HOL)_

The tool translates a TPTP problem statement formulated in a non-classical logic 
(using the logic specification format) into monomorphic or polymorphic THF.

For referencs, please use [![DOI](https://zenodo.org/badge/328684921.svg)](https://zenodo.org/badge/latestdoi/328684921)


## Logics
We refer to the TPTP non-classical logic extension at http://tptp.org/NonClassicalLogic/ for a description of the
logic specification format and the problem syntax.


Currently, only modal logics are supported:
| Logic family name  | Description |
| ------------- | ------------- |
| `$modal`  | Normal (quantified) modal logics, with box and diamond operator as `{$box}` and `{$diamond}`, respectively. Short forms: `[.]` for box and `<.>` for diamon. Modal operators can be indexed in both long and short forms, e.g., `{$box(#someindex)}` or `<#anotherindex>`.  |
| `$alethic_modal` | Same as `$modal` only that the operators are called `{$necessary}` and `{$possible}` instead (short forms are identical).  |
| `$deontic` | Same as `$modal` only that the operators are called `{$obligatory}` and `{$permissible}` instead (short forms are identical).  |
| `$alethic_modal` | Similar to `$modal` only that there is only one operator called `{$knows}` (short forms `[.]`).  |


 More logics will be added soon.

## Usage
An executable JAR file is distributed with the most current release. 


```
usage: embedproblem [-l <logic>] [-p <parameter>] [-s <spec>=<value>] [--tstp] <problem file> [<output file>]

 <problem file> can be either a file name or '-' (without parentheses) for stdin.
 If <output file> is specified, the result is written to <output file>, otherwise to stdout.

 Options:
  -l <logic>
     If <problem file> does not contain a logic specification statement, explicitly set
     the input format to <logic>. Ignored, if <problem file> contains a logic specification statement.
     Supported <logic>s are: $modal, $alethic_modal, $deontic_modal, $epistemic_modal

  -p <parameter>
     Pass transformation parameter <parameter> to the embedding procedure.

  -s <spec>=<value>
     If <problem file> does not contain a logic specification statement, explicitly set
     semantics of <spec> to <value>. In this case, -l needs to be provided.
     Ignored, if <problem file> contains a logic specification statement.

  --tstp
     Enable TSTP-compatible output: The output in <output file> (or stdout) will
     start with a SZS status value and the output will be wrapped within
     SZS BEGIN and SZS END block delimiters. Disabled by default.

  --version
     Prints the version number of the executable and terminates.

  --help
     Prints this description and terminates.
```


## Contact
In case of questions or comments, feel free to contact Alexander Steen (alexander.steen *at* uni-greifswald.de).

## Notes
The modal logic embedding is an extended and consolidated tool inspired by Tobias Gleißner's embedding tool at the leoprover/embed_modal repository.
This version makes use of the `scala-tptp-parser` library from leoprover/scala-tptp-parser that is much faster, in particular for larger input problems.
