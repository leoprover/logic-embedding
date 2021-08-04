%------------------------------------------------------------------------------
% File     : LCL870#1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Logic calculi
% Problem  : The Barcan formula is valid in quantified modal logic K
% Version  : Especial.
% English  : 

% Refs     : [Ste21] Steen (2021), Email to Geoff Sutcliffe
% Source   : [Ste21]
% Names    : ex2_quantification_bf.p [Ste21]
%          : SYM001+1 [QMLTP]

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : THN_THM_NEQ

% Comments : Short connectives
%------------------------------------------------------------------------------
thf(simple_s5,logic,(
    $modal ==
        [ $constants == $rigid,
          $quantification == $decreasing,
          $consequence == $global,
          $modalities == $modal_system_K ] )).

%----Specify an uninterpreted predicate symbol f
thf(f_type,type,f: $i > $o).

thf(barcan_formula,conjecture,
    ( ( ! [X: $i] : ( [.] @ (f @ X) ) )
   => ( [.] @ 
          ! [X: $i] : ( f @ X ) ) ) ).

%------------------------------------------------------------------------------
