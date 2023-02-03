logic-embedding
------
_A tool for embedding non-classical logics into higher-order logic (HOL)_

The tool translates a TPTP problem statement formulated in a non-classical logic 
(using the logic specification format) into monomorphic or polymorphic THF.
A description of the tool is available as tool paper [^2], the underlying TPTP syntax is
described in [^3].

For references to the tool, please use [![DOI](https://zenodo.org/badge/328684921.svg)](https://zenodo.org/badge/latestdoi/328684921)


## Logics
We refer to the TPTP non-classical logic extension at http://tptp.org/NonClassicalLogic/ for a description of the
logic specification format and the problem syntax.


Currently, the following logics (logic families) are supported:

| Logic family name | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
|-------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `$modal`          | Normal (quantified) multi-modal logics, with box and diamond operator as `{$box}` and `{$diamond}`, respectively. Short forms: `[.]` for box and `<.>` for diamon. Modal operators can be indexed in both long and short forms, e.g., `{$box(#someindex)}` or `<#anotherindex>`.                                                                                                                                                                                                                                                                                                                                                                  |
| `$alethic_modal`  | Same as `$modal` only that the operators are called `{$necessary}` and `{$possible}` instead (short forms are identical).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `$deontic`        | Same as `$modal` only that the operators are called `{$obligatory}` and `{$permissible}` instead (short forms are identical).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `$alethic_modal`  | Similar to `$modal` only that there is only one operator called `{$knows}` (short forms `[.]`).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `$$hybrid`        | Hybrid logics extend the modal logic family $modal with the notion of nominals, a special kind of atomic formula symbol that is true only in a specific world [2]. The logics represented by $$hybrid are first-order variants of H(E, @, ↓). A nominal symbol `n` is represented as `{$$nominal} @ (n)`, the shift operator @s as `{$$shift(#s)}`, and the bind operator ↓ x as `{$$bind(#X)}`. All other aspects are analogous to the modal logic representation above.                                                                                                                                                                            |
| `$$pal`           | Public announcement logic (PAL) is a propositional epistemic logic that allows for reasoning about knowledge. In contrast to $modal, PAL is a dynamic logic that supports updating the knowledge of agents via so-called announcement operators. The knowledge operator Ki is given by `{$$knows(#i)}`, the common knowledge operator CA , with A a set of agents, by `{$$common($$group := [...])}`, and the announcement [!ϕ] is represented as `{$$announce($$formula := phi)}`.                                                                                                                                                               |
| `$$ddl`           | Deontic logics are formalisms for reasoning over norms, obligations, permissions and prohibitions. In contrast to modal logics used for this purpose (e.g., modal logic D), dyadic deontic logics (DDLs), named $$ddl, offer a more sophisticated representation of conditional norms using a dyadic obligation operator O(ϕ/ψ). They address paradoxes of other deontic logics in the context of so-called contrary-to-duty (CTD) situations. The concrete DDLs supported are the propositional system by Carmo and Jones and Åqvist’s propositional system E. The dyadic deontic operator O is represented by `{$$obl}` (short for obligatory). |
| `$$normative`     | Normative meta form, a semantically underspecified format for expressing deontic logic concepts. Can be translated into standard deontic logic (SDL/modal logics) or DDL (see above) as desired, see [^1] for details. Conditional obligations, permissions, prohibitions and expressied via `{$$obligation} @ (body, head)`, `{$$permission} @ (body, head)`, and `{$$prohibition} @ (body, head)`, respectively. Counts-as norms (constitutional norms) are expressed via `{$$constitutive} @ (body, head)`. It depends on the target logic how these concepts are compiled into a concrete logical format.                                                 |

### Logic specifications
Non-classical logic languages quite commonly admit different concrete logics using the same syntax. In order to chose the exact logic intended for the input
problem, suitable parameters are given as properties to the logic specification:

| Logic family name | Parameter         | Description                                                                                                                                                                                                                                                                                                                                                     |
|-------------------|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `$modal`          | `$quantification` | Selects whether quantification semantics is varying domains, constant domains, cumulative domains or decreasing domains.<br><br>Accepted values: `$varying`, `$constant`, `$cumulative`, `$decreasing`                                                                                                                                                          |
|                   | `$constants`      | Selects whether constant and functions symbols are interpreted as rigidor flexible.<br><br> Accepted values: `$rigid`, `$flexible`                                                                                                                                                                                                                              |
|                   | `$modalities`     | Selects the properties for the modal operators.<br><br> Accepted values, for each modality: `$modal_system_X` where `X` ∈ {`K`, `KB`, `K4`, `K5`, `K45`, `KB5`, `D`, `DB`, `D4`, `D5`, `D45`, `T`, `B`, `S4`, `S5`, `S5U`} <br>_or a list of axiom schemes_<br> [`$modal axiom X1` , ..., `$modal axiom Xn` ] `Xi` ∈ {`K`, `T`, `B`, `D`, `4`, `5`, `CD`, `C4`} |
| `$$hybrid`        | _same as `$modal`_ |                                                                                                                                                                                                                                                                                                                                                                 |
| `$$pal`           | _none_            |                                                                                                                                                                                                                                                                                                                                                                 |
| `$$ddl`           | `$$system`        | Selects which DDL logic system is employed: Carmo and Jones or Åqvist's system E.<br><br>Accepted values: `$$carmoJones` or `$$aqvistE`                                                                                                                                                                                                                         |
| `$$normative`     | `$logic`        | Selects which deontic logic system should be used for compiling the semantically underspecified statements into concrete expressions. <br><br> Accepted values: `$$sdl` for SDL, `$$carmoJones` for the DDL of Carmo and Jones, `$$aqvistE` for Aqvist's DDL E                                                                                             |                                                                                                                                                                                                                                                                                                                                                            |

### Examples

#### Logic `$modal`
The so-called Barcan formula is a modal logic formula that is valid if and only if the quantification domain of the underlying first-order
modal logic model is non-cumulative.

```
  tff(modal_k5, logic, $modal == [
     $constants == $rigid,
     $quantification == $decreasing,
     $modalities == [$modal_axiom_K, $modal_axiom_5]
   ] ).

  tff(bf, conjecture, ( ![X]: ({$box} @ (f(X))) ) => {$box} @ (![X]: f(X)) ).
```

#### Logic `$$hybrid`

```
  tff(hybrid_s5,logic, $$hybrid == [
      $constants == $rigid,
      $quantification == $varying,
      $modalities == $modal_system_S5
    ] ).

  tff(1, conjecture, ![X]: ({$box} @ ({$$shift(#n)} @ (
             {$$bind(#Y)} @ ((Y & p(X))
                          <=>
                          ({$$nominal} @ (n) & p(X))
                     )))) ).
```

#### Logic `$$pal`

```
tff(pal, logic, $$pal == []).

tff(c, conjecture, {$$announce($$formula := p)} @ ( {$$common($$group := [a,b,c,k])} @ (p) )).
```

#### Logic `$$ddl`


```
  tff(spec_e, logic, $$ddl == [ $$system == $$aqvistE ] ).

  tff(a1, axiom, {$$obl} @ (go,$true)).
  tff(a2, axiom, {$$obl} @ (tell, go)).
  tff(a3, axiom, {$$obl} @ (~tell, ~go)).
  tff(situation, axiom, ~go). 
  tff(c, conjecture, {$$obl} @ (~tell,$true)).
```
This example encodes that (a1) you ought to go and help your neighbor, (a2) if you go then you ought to tell him/her that you are coming,
and (a3) if you don't go, then you ought not tell him/her. It can consistently be inferred that, if you actually don't go, then you ought not
tell.

### Extended specifications

#### Modal logic `$modal`

Multiple modal operators are defined like ...
```
thf(advanced,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification == $cumulative,
        $modalities ==
          [ $modal_system_S5,
            [#a] == $modal_system_KB,
            [#b] == $modal_system_K ] ] )).
```
Here box operator a is system KB, box operator b is K. Of course, also lists of axiom schemes can be used. All further modal operators are S5 (if existent).

Distinct quantification semantics for each type are defined like ...
```
thf(quantification,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification ==
          [ $constant,
            human_type == $varying ],
        $modalities == $modal_system_S5 ] )).
```
Here, every quantification over variables of type `human_type` are varying domain, all others constant domain.


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
     Supported <logic>s are: $modal, $epistemic_modal, $$ddl, $$pal, $alethic_modal, $$hybrid, $deontic_modal

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


[^1]: A. Steen, D. Fuenmayor. Bridging between LegalRuleML and TPTP for Automated Normative Reasoning. In: 6th International Joint Conference on Rules and Reasoning Berlin, 26-28 September 2022, Lecture Notes in Computer Science, Vol.13752, pp. 244--260, Springer, 2022. DOI: https://doi.org/10.1007/978-3-031-21541-4_16.
[^2]: A. Steen. An Extensible Logic Embedding Tool for Lightweight Non-Classical Reasoning. In Eighth Workshop on Practical Aspects of Automated Reasoning (PAAR 2022). CEUR Workshop Proceedings, Vol. 3201, CEUR-WG.org, 2022. Available at https://ceur-ws.org/Vol-3201/paper13.pdf.
[^3]: A. Steen, D. Fuenmayor, T. Gleißner, G. Sutcliffe and C. Benzmüller. Automated Reasoning in Non-classical Logics in the TPTP World. In Eighth Workshop on Practical Aspects of Automated Reasoning (PAAR 2022). CEUR Workshop Proceedings, Vol. 3201, CEUR-WG.org, 2022. Available at https://ceur-ws.org/Vol-3201/paper11.pdf.
