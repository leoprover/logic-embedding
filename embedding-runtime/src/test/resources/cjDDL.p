tff(spec, logic, $$ddl == [ $$system == $$carmoJones ] ).

tff(1, axiom, {$$obl} @ (go, $true) ).
tff(2, axiom, {$$obl} @ (tell, go) ).
tff(3, axiom, {$$obl} @ (~tell, ~go) ).
tff(4, axiom, ~go ).
