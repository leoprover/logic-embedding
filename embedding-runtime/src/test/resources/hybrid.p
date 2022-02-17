tff(hybrid_s5,logic,(
    $$hybrid ==
        [ $constants == $rigid,
          $quantification == $varying,
          $modalities == $modal_system_S5 ] )).

%tff(1, conjecture, (<.>({$$nominal}(n) & p) & <.>({$$nominal}(n) & q)) => <.>(p & q) ).
%tff(1, conjecture, ![X]:( (<.>({$$nominal}(n) & p(X)) & <.>({$$nominal}(n) & q(X))) => <.>(p(X) & q(X))) ).
%tff(1, conjecture, {$$shift(#n)}(n)).
%tff(1, conjecture, {$$shift(#m)}({$$shift(#n)}(n))).
tff(1, conjecture, {$$shift(#n)}({$$bind(#X)}(X <=> {$$nominal}(n)))).
