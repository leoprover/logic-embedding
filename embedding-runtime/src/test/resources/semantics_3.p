%----Default modality S5 as list of axioms K + T + 5
thf(simple_s5_v3,logic,(
    $modal :=
      [ $constants := $rigid,
        $quantification := $constant,
        $consequence := $global,
        $modalities :=
          [ $modal_axiom_K,
            $modal_axiom_T,
            $modal_axiom_5 ] ] )).
            
%--- does ϕ → □◇ϕ hold?
thf(mysterious, conjecture, ![A:$o]: (A => ($box @ ($dia @ A))) ).
