tff(pal, logic, $$pal == []).

%tff(c, conjecture, [#k] p).
%tff(c, conjecture, {$$common($$group := [a,b,c,k])} @ (p) => {$$knows(#k)} @ (p)).

tff(c, conjecture, {$$announce($$formula := p)} @ (p)).
