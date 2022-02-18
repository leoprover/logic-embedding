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
| `$$hybrid` | Hybrid logics extend the modal logic family $modal with the notion of nominals, a special kind of atomic formula symbol that is true only in a specific world [2]. The logics represented by $$hybrid are first-order variants of H(E, @, ↓). A nominal symbol `n` is represented as `{$$nominal}(n)`, the shift operator @s as `{$$shift(#s)}`, and the bind operator ↓ x as `{$$bind(#X)}`. All other aspects are analogous to the modal logic representation above.|
| `$$pal` | Public announcement logic (PAL) is a propositional epistemic logic that allows for reasoning about knowledge. In contrast to $modal, PAL is a dynamic logic that supports updating the knowledge of agents via so-called announcement operators. The knowledge operator Ki is given by `{$$knows(#i)}`, the common knowledge operator CA , with A a set of agents, by `{$$common($$group := [...])}`, and the announcement [!ϕ] is represented as `{$$announce($$formula := phi)}`. |
| `$$ddl` | Deontic logics are formalisms for reasoning over norms, obligations, permissions and prohibitions. In contrast to modal logics used for this purpose (e.g., modal logic D), dyadic deontic logics (DDLs), named $$ddl, offer a more sophisticated representation of conditional norms using a dyadic obligation operator O(ϕ/ψ). They address paradoxes of other deontic logics in the context of so-called contrary-to-duty (CTD) situations. The concrete DDLs supported are the propositional system by Carmo and Jones and Åqvist’s propositional system E. The dyadic deontic operator O is represented by `{$$obl}` (short for obligatory). |

### Logic specifications
Non-classical logic languages quite commonly admit different concrete logics using the same syntax. In order to chose the exact logic intended for the input
problem, suitable parameters are given as properties to the logic specification:

| Logic family name  | Parameter | Description |
| ------------- | ------------- |  ------------- |
| `$modal` | `$quantification` | Selects whether quantification semantics is varying domains, constant domains, cumulative domains or decreasing domains.<br><br>Accepted values: `$varying`, `$constant`, `$cumulative`, `$decreasing` |
|  | `$constants` | Selects whether constant and functions symbols are interpreted as rigidor flexible.<br><br> Accepted values: `$rigid`, `$flexible` |
|  | `$modalities` | Selects the properties for the modal operators.<br><br> Accepted values, for each modality: `$modal_system_X` where `X` ∈ {`K`, `KB`, `K4`, `K5`, `K45`, `KB5`, `D`, `DB`, `D4`, `D5`, `D45`, `T`, `B`, `S4`, `S5`, `S5U`} <br>_or a list of axiom schemes_<br> [`$modal axiom X1` , ..., `$modal axiom Xn` ] `Xi` ∈ {`K`, `T`, `B`, `D`, `4`, `5`, `CD`, `C4`} |
| `$$hybrid` | _same as `$modal`_ | |
| `$$pal` | _none_ | |
| `$$ddl` | `$$system` | Selects which DDL logic system is employed: Carmo and Jones or Åqvist's system E.<br><br>Accepted values: `$$carmoJones` or `$$aqvistE` |



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
