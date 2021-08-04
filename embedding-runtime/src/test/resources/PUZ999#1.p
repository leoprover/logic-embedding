%------------------------------------------------------------------------------
% File     : PUZ999#1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Puzzles
% Problem  : The Bungling Chemist
% Version  : Especial.
% English  : Assume that a chemical compound c is made by pouring the elements 
%            a and b into the same beaker. The two elements a and b are not 
%            acid. It is possible that after making the compound c it results
%            acid. Then it is possible that pouring element a results not acid 
%            and pouring a and b in the beaker results acid

% Refs     : [Bal98] Baldoni (1998), Normal Multimodal Logics: Automatic De
% Source   : [TPTP]
% Names    : 

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : THN_THM_NEQ

% Comments : Long connectives
%------------------------------------------------------------------------------
thf(simple_s5,logic,(
    $alethic_modal ==
        [ $constants == $rigid,
          $quantification == $cumulative,
          $consequence == $global,
          $modalities == $modal_system_S5 ] )).

thf(acid_type,type,acid: $o).

thf(pour_ab_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_a} @
        ( {$necessary:#pour_b} @ acid ) )
   => ( {$necessary:#pour_c} @ acid ) ) )).

thf(pour_ab_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_a} @
        ( {$necessary:#pour_b} @ (~ acid) ) )
   => ( {$necessary:#pour_c} @ (~ acid) ) ) )).
  
thf(pour_ba_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a} @ acid ) )
   => ( {$necessary:#make_c} @ acid ) ) )).

thf(pour_ba_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a} @ (~ acid) ) )
   => ( {$necessary:#make_c} @ (~ acid) ) ) )).
    
thf(pour_ab_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_a} @
        ( {$necessary:#pour_b} @ acid ) )
   => ( {$necessary:#pour_c} @ acid ) ) )).

thf(pour_ab_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_a} @
        ( {$necessary:#pour_b} @ (~ acid) ) )
   => ( {$necessary:#pour_c} @ (~ acid) ) ) )).
  
thf(pour_ba_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a} @ acid ) )
   => ( {$necessary:#make_c} @ acid ) ) )).

thf(pour_ba_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a} @ (~ acid) ) )
   => ( {$necessary:#make_c} @ (~ acid) ) ) )).
    
thf(pour_ab_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_a} @ 
        ( {$necessary:#pour_b} @ acid ) )
   => ( {$necessary:#pour_c} @ acid ) ) )).

thf(pour_ab_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_a} @
        ( {$necessary:#pour_b} @ (~ acid) ) )
   => ( {$necessary:#pour_c} @ (~ acid) ) ) )).
  
thf(pour_ba_make_axiom_1,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a} @ acid ) )
   => ( {$necessary:#make_c} @ acid ) ) )).

thf(pour_ba_make_axiom_2,axiom,(
    ( ( {$necessary:#pour_b} @
        ( {$necessary:#pour_a}@ (~ acid) ) )
   => ( {$necessary:#make_c} @ (~ acid) ) ) )).
    
thf(pour_a_acid,axiom,(
    {$necessary:#pour_a} @ (~ acid) )).

thf(make_c_acid,axiom,(
    {$possible:#make_c} @ (acid) )).

thf(possible_acid,conjecture,(
    ( ( {$possible:#pour_a} @ (~ acid) )
    & ( {$possible:#pour_a} @
        ( {$possible:#pour_b} @ acid ) ) ) )).

%------------------------------------------------------------------------------
