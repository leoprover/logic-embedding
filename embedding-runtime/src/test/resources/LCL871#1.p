%------------------------------------------------------------------------------
% File     : LCL871#1 : TPTP v9.0.0. Released v9.0.0.
% Domain   : Logic calculi
% Problem  : The Converse Barcan formula is valid in quantified modal logic K
% Version  : Especial.
% English  : 

% Refs     : [Ste21] Steen (2021), Email to Geoff Sutcliffe
% Source   : [Ste21]
% Names    : ex2_quantification_cbf.p [Ste21]
%          : SYM002+1 [QMLTP]

% Status   : Theorem
% Rating   : ? v9.0.0
% Syntax   : TBA
% SPC      : THN_THM_NEQ

% Comments : Short connectives
%------------------------------------------------------------------------------
thf(simple_s5,logic,(
    $modal ==
        [ $constants == $rigid,
          $quantification == $cumulative,
          $consequence == $global,
          $modalities == $modal_system_K ] )).

%----Specify an uninterpreted predicate symbol f
thf(f_type,type,f: $i > $o).

thf(converse_barcan_formula,conjecture,
    ( ( [.] @ 
          ! [X: $i] : ( f @ X ) )
   => ( ! [X: $i] : ( [.] @ (f @ X) ) ) ) ).

%------------------------------------------------------------------------------
