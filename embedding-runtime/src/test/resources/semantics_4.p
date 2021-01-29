%----Default modality S5 as list of axioms K + T + 5
thf(simple_s5_v3,logic,(
    $modal :=
      [ $constants := $rigid,
        $quantification := $constant,
        $consequence := $global,
        $modalities :=
          [ $modal_system_S5, $box_int @ 1 := $modal_system_S4] ] )).
            
thf(mysterious, conjecture, ![A:$o]: (A => ($box_int @ 0 @ ($box_int @ 1 @ A))) ).
