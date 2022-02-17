tff(hybrid_s5,logic,(
    $$hybrid ==
        [ $constants == $rigid,
          $quantification == $varying,
          $modalities == $modal_system_S5 ] )).

tff(1, conjecture, (<.>({$$nominal}(n) & p) & <.>({$$nominal}(n) & q)) => <.>(p & q) ).

