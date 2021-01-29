%----Standard S5
thf(simple_s5,logic,(
    $modal :=
      [ $constants := $rigid,
        $quantification := $constant,
        $consequence :=
          [ $global ],
        $modalities := $modal_system_S5 ] )).
            
%--- does ϕ → □◇ϕ hold?
thf(mysterious, conjecture, ![A:$o]: (A => ($box @ ($dia @ A))) ).
