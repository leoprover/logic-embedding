logic-embedding
------
_A tool for embedding non-classical logics into higher-order logic (HOL)_

The tool translates a TPTP problem statement formulated in a non-classical logic 
(using the logic specification format) into classical higher-order logic
(THF format) or first-order logic (TFF format), either using monomorphic or polymorphic types.
A description of the tool is available as tool paper [^2], the underlying TPTP syntax is
described in [^3].

For references to the tool, please use [![DOI](https://zenodo.org/badge/328684921.svg)](https://zenodo.org/badge/latestdoi/328684921)


## Logics
We refer to the TPTP non-classical logic extension at http://tptp.org/NonClassicalLogic/ for a description of the
logic specification format and the problem syntax.


Currently, the following logics (logic families) are supported:

| Logic family name  | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
|--------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `$modal`           | Normal (quantified) multi-modal logics, with box and diamond operator as `{$box}` and `{$dia}`, respectively. Short forms: `[.]` for box and `<.>` for diamond. Modal operators can be indexed in long form, e.g., `{$box(#someindex)}`.                                                                                                                                                                                                                                                                                                                                                                                                          |
| `$alethic_modal`   | Same as `$modal` only that the operators are called `{$necessary}` and `{$possible}` instead (short forms are identical).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `$deontic_modal`   | Same as `$modal` only that the operators are called `{$obligatory}` and `{$permissible}` instead (short forms are identical).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `$epistemic_modal` | Same as `$modal` only that the operators are called `{$knows}` and `{$canKnow}` instead (short forms are identical).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `$$hybrid`         | Hybrid logics extend the modal logic family `$modal` with the notion of nominals, a special kind of atomic formula symbol that is true only in a specific world [2]. The logics represented by $$hybrid are first-order variants of H(E, @, ↓). A nominal symbol `n` is represented as `{$$nominal} @ (n)`, the shift operator @s as `{$$shift(#s)}`, and the bind operator ↓ x as `{$$bind(#X)}`. All other aspects are analogous to the modal logic representation above.                                                                                                                                                                         |
| `$$pal`            | Public announcement logic (PAL) is a propositional epistemic logic that allows for reasoning about knowledge. In contrast to $modal, PAL is a dynamic logic that supports updating the knowledge of agents via so-called announcement operators. The knowledge operator Ki is given by `{$$knows(#i)}`, the common knowledge operator CA , with A a set of agents, by `{$$common($$group := [...])}`, and the announcement [!ϕ] is represented as `{$$announce($$formula := phi)}`.                                                                                                                                                               |
| `$$ddl`            | Deontic logics are formalisms for reasoning over norms, obligations, permissions and prohibitions. In contrast to modal logics used for this purpose (e.g., modal logic D), dyadic deontic logics (DDLs), named $$ddl, offer a more sophisticated representation of conditional norms using a dyadic obligation operator O(ϕ/ψ). They address paradoxes of other deontic logics in the context of so-called contrary-to-duty (CTD) situations. The concrete DDLs supported are the propositional system by Carmo and Jones and Åqvist’s propositional system E. The dyadic deontic operator O is represented by `{$$obl}` (short for obligatory). |
| `$$normative`      | Normative meta form, a semantically underspecified format for expressing deontic logic concepts. Can be translated into standard deontic logic (SDL/modal logics) or DDL (see above) as desired, see [^1] for details. Conditional obligations, permissions, prohibitions and expressied via `{$$obligation} @ (body, head)`, `{$$permission} @ (body, head)`, and `{$$prohibition} @ (body, head)`, respectively. Counts-as norms (constitutional norms) are expressed via `{$$constitutive} @ (body, head)`. It depends on the target logic how these concepts are compiled into a concrete logical format.                                     |
| `$$dhol`           | Dependently-typed higher-order logic, as defined by [^5]. |
| `$$dholtc`         | Embedding of type checking constraints for dependently-typed HOL, as defined by TBA (CITE?) |

### Logic specifications
Non-classical logic languages quite commonly admit different concrete logics using the same syntax. In order to chose the exact logic intended for the input
problem, suitable parameters are given as properties to the logic specification:

| Logic family name | Parameter          | Description                                                                                                                                                                                                                                                                                                                                                     |
|-------------------|--------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `$modal`          | `$domains`         | Selects whether quantification semantics is varying domains, constant domains, cumulative domains or decreasing domains.<br><br>Accepted values: `$varying`, `$constant`, `$cumulative`, `$decreasing`                                                                                                                                                          |
|                   | `$designation`     | Selects whether non-logical symbols (constants and function symbols) have rigid or flexible designation (i.e., the same interpretation in all worlds, or possibly different ones in different worlds).<br><br> Accepted values: `$rigid`, `$flexible`                                                                                                           |
|                   | `$terms`     | Selects whether terms, in each world `w`, are interpreted as elements from the respective domain at `w` (i.e., whether they exist in that world); this case is referred to as local terms. With global terms, terms may be interpreted as elements from arbitrary worlds (i.e., in particular, the interpretation of a term at a specific world may not exist exist at that world). <br><br> Accepted values: `$local`, `$global`                                                                                                           |
|                   | `$modalities`      | Selects the properties for the modal operators.<br><br> Accepted values, for each modality: `$modal_system_X` where `X` ∈ {`K`, `KB`, `K4`, `K5`, `K45`, `KB5`, `D`, `DB`, `D4`, `D5`, `D45`, `T`, `B`, `S4`, `S5`, `S5U`} <br>_or a list of axiom schemes_<br> [`$modal axiom X1` , ..., `$modal axiom Xn` ] `Xi` ∈ {`K`, `T`, `B`, `D`, `4`, `5`, `CD`, `C4`} |
| `$$hybrid`        | _same as `$modal`_ (except that `$terms` is not available, yet). |                                                                                                                                                                                                                                                                                                                                                                 |
| `$$pal`           | _none_             |                                                                                                                                                                                                                                                                                                                                                                 |
| `$$ddl`           | `$$system`         | Selects which DDL logic system is employed: Carmo and Jones or Åqvist's system E.<br><br>Accepted values: `$$carmoJones` or `$$aqvistE`                                                                                                                                                                                                                         |
| `$$normative`     | `$logic`           | Selects which deontic logic system should be used for compiling the semantically underspecified statements into concrete expressions. <br><br> Accepted values: `$$sdl` for SDL, `$$carmoJones` for the DDL of Carmo and Jones, `$$aqvistE` for Aqvist's DDL E                                                                                                  |                                                                                                                                                                                                                                                                                                                                                            |
| `$$dhol`          | _none_             |               |
| `$$dholtc`        | _none_             |               |

### Examples

#### Logic `$modal`
The so-called Barcan formula is a modal logic formula that is valid if and only if the quantification domain of the underlying first-order
modal logic model is non-cumulative.

```
  tff(modal_k5, logic, $modal == [
     $designation == $rigid,
     $domains == $decreasing,
     $terms == $local,
     $modalities == [$modal_axiom_K, $modal_axiom_5]
   ] ).

  tff(bf, conjecture, ( ![X]: ({$box} @ (f(X))) ) => {$box} @ (![X]: f(X)) ).
```

#### Logic `$$hybrid`

```
  tff(hybrid_s5,logic, $$hybrid == [
      $designation == $rigid,
      $domains == $varying,
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
tff(pal, logic, $$pal).

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

#### Modal logic `$modal`: Per-modality specification

Multiple modal operators are defined like ...
```
thf(advanced,logic,(
    $modal ==
      [ $designation == $rigid,
        $domains == $cumulative,
        $terms == $global,
        $modalities ==
          [ $modal_system_S5,
            {$box(#a)} == $modal_system_KB,
            {$box(#b)} == $modal_system_K ] ] )).
```
Here box operator a is system KB, box operator b is K. Of course, also lists of axiom schemes can be used. All further modal operators are S5 (if existent).

#### Modal logic `$modal`: Per-type quantification specification

Distinct quantification semantics for each type are defined like ...
```
thf(quantification,logic,(
    $modal ==
      [ $designation == $rigid,
        $domains ==
          [ $constant,
            human_type == $varying ],
        $terms == $global,
        $modalities == $modal_system_S5 ] )).
```
Here, every quantification over variables of type `human_type` are varying domain, all others constant domain.

#### Modal logic `$modal`: Including interaction axiom schemes

Axiom schemas acting as interaction axioms between different modalities, can simply
be added as part of the `$modality` entry (see also [^4]):
```
tff(modal_system,logic,
    $modal == 
      [ $designation == $rigid,
        $domains == $cumulative,
        $terms == $local,
        $modalities == [
          {$box(#always)} == $modal_system_S4,
          {$box(#load)} == $modal_system_K,
          {$box(#shoot)} == $modal_system_K,
			    {$box(#always)} @ (P) => {$box(#load)} @ (P),
			    {$box(#always)} @ (P) => {$box(#shoot)} @ (P) ] ] ).
```



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
[^2]
## Contributors
The logic embedding tool received valuable contributions by several people. See the `CONTRIBUTORS` file for details.

## Notes
The modal logic embedding is an extended and consolidated tool inspired by Tobias Gleißner's embedding tool at the leoprover/embed_modal repository.
This version makes use of the `scala-tptp-parser` library from leoprover/scala-tptp-parser that is much faster, in particular for larger input problems.


[^1]: A. Steen, D. Fuenmayor. Bridging between LegalRuleML and TPTP for Automated Normative Reasoning. In: 6th International Joint Conference on Rules and Reasoning Berlin, 26-28 September 2022, Lecture Notes in Computer Science, Vol.13752, pp. 244--260, Springer, 2022. DOI: https://doi.org/10.1007/978-3-031-21541-4_16.
[^2]: A. Steen. An Extensible Logic Embedding Tool for Lightweight Non-Classical Reasoning. In Eighth Workshop on Practical Aspects of Automated Reasoning (PAAR 2022). CEUR Workshop Proceedings, Vol. 3201, CEUR-WG.org, 2022. Available at https://ceur-ws.org/Vol-3201/paper13.pdf.
[^3]: A. Steen, D. Fuenmayor, T. Gleißner, G. Sutcliffe and C. Benzmüller. Automated Reasoning in Non-classical Logics in the TPTP World. In Eighth Workshop on Practical Aspects of Automated Reasoning (PAAR 2022). CEUR Workshop Proceedings, Vol. 3201, CEUR-WG.org, 2022. Available at https://ceur-ws.org/Vol-3201/paper11.pdf.
[^4]: M. Taprogge, A. Steen. Flexible Automation of Quantified Multi-Modal Logics with Interaction. In KI 2023: Advances in Artificial Intelligence. 46th German Conference on AI, Berlin, Germany, September 26–29, 2023, Proceedings, LNCS, Vol. 14236, Springer, 2023. 
[^5]: C. Rothgang, F. Rabe, and C. Benzmüller. Theorem Proving in Dependently Typed Higher-Order Logic. In B. Pientka and C. Tinelli, editors, Automated Deduction, pages 438–455. Springer, 2023.
