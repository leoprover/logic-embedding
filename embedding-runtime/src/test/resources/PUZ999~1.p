%------------------------------------------------------------------------------
% File     : PUZ999~1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Puzzles
% Problem  : The Bungling Chemist
% Version  : Especial.
% English  : Assume that a chemical compound c is made by pouring the elements 
%            a and b into the same beaker. The two elements a and b are not 
%            acid. It is possible that after making the compound c it results
%            acid. Then it is possible that pouring element a results not acid 
%            and pouring a and b in the beaker results acid

% Refs     : [Bal98] Baldoni (1998), Normal Multimodal Logics: Automatic De
% Source   : [QMLTP]
% Names    : MML006+1.p [QMLTP]

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : TFN_THM_NEQ

% Comments : Short connectives
%------------------------------------------------------------------------------
tff(simple_s5,logic,(
    $alethic_modal ==
        [ $constants == $rigid,
          $quantification == $cumulative,
          $consequence == $global,
          $modalities == $modal_system_S5 ] )).

tff(acid_type,type,acid: $o).

tff(pour_ab_make_axiom_1,axiom,(
    ( [#pour_a](
        [#pour_b](acid))
   => [#pour_c](acid) ) )).

tff(pour_ab_make_axiom_2,axiom,(
    ( [#pour_a](
        [#pour_b](~ acid))
   => [#pour_c](~ acid) ) )).
  
tff(pour_ba_make_axiom_1,axiom,(
    ( [#pour_b](
        [#pour_a](acid))
   => [#make_c](acid) ) )).

tff(pour_ba_make_axiom_2,axiom,(
    ( [#pour_b](
        [#pour_a](~ acid))
   => [#make_c](~ acid) ) )).
    
tff(pour_ab_make_axiom_1,axiom,(
    ( [#pour_a](
        [#pour_b](acid))
   => [#pour_c](acid) ) )).

tff(pour_ab_make_axiom_2,axiom,(
    ( [#pour_a](
        [#pour_b](~ acid))
   => [#pour_c](~ acid) ) )).
  
tff(pour_ba_make_axiom_1,axiom,(
    ( [#pour_b] (
        [#pour_a](acid))
   => [#make_c](acid) ) )).

tff(pour_ba_make_axiom_2,axiom,(
    ( [#pour_b] (
        [#pour_a](~ acid))
   => [#make_c](~ acid) ) )).
    
tff(pour_ab_make_axiom_1,axiom,(
    ( [#pour_a](
        [#pour_b](acid))
   => [#pour_c](acid) ) )).

tff(pour_ab_make_axiom_2,axiom,(
    ( [#pour_a](
        [#pour_b](~ acid))
   => [#pour_c](~ acid) ) )).
  
tff(pour_ba_make_axiom_1,axiom,(
    ( [#pour_b] (
        [#pour_a](acid))
   => [#make_c](acid) ) )).

tff(pour_ba_make_axiom_2,axiom,(
    ( [#pour_b] (
        [#pour_a](~ acid))
   => [#make_c](~ acid) ) )).
    
tff(pour_a_acid,axiom,(
    [#pour_a](~ acid) )).

tff(make_c_acid,axiom,(
    <#make_c>(acid) )).

tff(possible_acid,conjecture,(
    ( <#pour_a>(~ acid)
    & <#pour_a>(
        <#pour_b>(acid)) ) )).

%------------------------------------------------------------------------------
