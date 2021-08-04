%----Standard S5
thf(simple_s5,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification == $constant,
        $consequence == $global,
        $modalities == $modal_system_S5 ] )).

%----Constants The constant king_of_france has special semantics
thf(human_type,type,(
    human: $tType )).

thf(king_of_france_constant,type,(
    king_of_france: human )).

thf(constants,logic,(
    $modal ==
      [ $constants ==
          [ $constant,
            king_of_france == $flexible ],
        $quantification == $constant,
        $consequence == $global,
        $modalities == $modal_system_S5 ] )).

%----Quantification may be different for any base type or compound type e.g.
%----for type plushie
thf(plushie_type,type,(
    plushie: $tType )).

thf(quantification,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification ==
          [ $constant,
            plushie == $varying ],
        $consequence == $global,
        $modalities == $modal_system_S5 ] )).

thf(different_modality,logic,(
    $modal == 
      [ $constants == $rigid,
        $quantification ==
          [ $constant,
            plushie == $varying ],
        $consequence == $global,
        $modalities == 
          [ $modal_system_S4,
            king_of_france == $modal_system_S5 ] ] )).

%----Consequence. All axioms same consequence except for ax1 which has a
%----special consequence
thf(ax1,axiom,(
    $true )).

thf(different_consequence,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification == $constant,
        $consequence ==
          [ $global,
            ax1 == $local ],
        $modalities == $modal_system_S5 ] )).

%----It's not clear if/how these might be supported - just putting out ideas here.
%----Something more exotic. a, b, and c are indices for multi-modal 
%----operators, e.g., If a is a $int, it could be used with $box_int
%----in an expression such as $box_int @ a @ p.
thf(exotic,logic,(
    $modal ==
      [ $constants == $flexible,
        $quantification == $cumulative,
        $consequence ==
          [ $global,
            ax1 == $local ],
        $modalities ==
          [ a == $modal_system_S5,
            b == $modal_system_KB,
            c == $modal_system_K ] ] )).

thf(quantification,logic,( 
    $modal ==
      [ $constants == $rigid,
        $quantification == $constant,
        $consequence == $global,
        $modalities ==
          ! [X: $int] :
            $ite($greater @ X @ 0,$modal_system_K,$modal_system_KB)] )).

thf(instantiated_modality,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification == $constant,
        $consequence == $global,
        $modalities ==
          [ $modal_axiom_K,
            archer == $modal_system_D ] ] )).

thf(funky_mixed,logic,(
    [ $modal ==
        [ $constants == $rigid,
          $quantification == $constant,
          $consequence == $global,
          $modalities == $modal_system_S5 ],
      $dialetheic ==
        [ $truth_values ==
            [ $true,
              $false,
              $both ],
          $embedding == $translational ] ] )).

%----Default modality S5 as list of axioms K + T + 5. This is currently not 
%----supported.
thf(simple_s5_v3,logic,(
    $modal ==
      [ $constants == $rigid,
        $quantification == $constant,
        $consequence == $global,
        $modalities ==
          [ $modal_axiom_K,
            $modal_axiom_T,
            $modal_axiom_5 ] ] )).
