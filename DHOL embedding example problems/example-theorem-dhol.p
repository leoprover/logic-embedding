tff(dhol, logic, $$dhol == []).
thf(obj_type,type,
	(obj: $tType) ).
thf(mor_type,type,
	mor: !> [X:obj]: (!> [Y:obj]: $tType) ).
thf(id_type,type,
	(id: !> [X:obj]: mor(X,X)) ).
thf(comp_type,type,
	(comp: !> [X:obj]: (!> [Y:obj]:  (!> [Z:obj]: (!> [F:mor(X,Y)]: (!> [G:mor(Y,Z)]:  mor(X,Z)))))) ).
thf(ax1,axiom,
	! [X:obj,Y:obj,M:mor(X,Y)]: (comp(X,X,Y,id(X),M) = M) ).
thf(ax2,axiom,
	! [X:obj,Y:obj,M:mor(X,Y)]: (comp(X,Y,Y,M,id(Y)) = M) ).
thf(ax3,axiom,! [X:obj,Y:obj,Z:obj,A:obj,F:mor(X,Y),G:mor(Y,Z),H:mor(Z,A)]: (comp(X,Y,A,F,comp(Y,Z,A,G,H))=comp(X,Z,A,comp(X,Y,Z,F,G),H)) ).
 thf(conj1,conjecture, ! [X:obj, Y:obj]: ((X = Y) => ((id(X)) = (id(Y)))) ).
%%% thf(conj2,conjecture, ! [X:obj, Y:obj, Z:obj, F:mor(X, Y), G:mor(Y,Z)]: (((X=Y) & (Y=Z) & (F=id(X)) & (G=id(Y))) => (comp(X,Y,Z,F,G) = id (Z))) ).
%%% thf(conj3,conjecture, ! [X:obj, Y:obj, Z:obj, F:mor(X,Y), G:mor(Y,X)]: (((comp(X,Y,X,F,G)=id(X)) & (comp(Y,X,Y,G,F)=id(Y))) => (! [H:mor(X,Z)]: (comp(X,Y,Z,F,comp(Y,X,Z,G,H))=H))) ).
%%% thf(conj4,conjecture, ! [X:obj, Y:obj, Z:obj, F:mor(X,Y), G:mor(Y,X)]: (((comp(X,Y,X,F,G)=id(X)) & (comp(Y,X,Y,G,F)=id(Y))) => (! [H:mor(X,Z)]: (comp(X,Y,Z,F,comp(Y,X,Z,G,H))= comp(X,X,Z,(comp(X,Y,X,F,G)),H) ))) ).
%%% thf(conj5,conjecture, ! [X:obj, Y:obj, Z:obj, F:mor(X,Y), G:mor(Y,X), H:mor(Y,Z), J:mor(Z,Y)]: ( ((comp(X,Y,X,F,G)=id(X)) & (comp(Y,X,Y,G,F)=id(Y))) => (((comp(Y,Z,Y,H,J)=id(Y)) & (comp(Z,Y,Z,J,H)=id(Z))) => (! [K:mor(X,Z)]: (comp(X,Z,Z, (comp(X,Y,Z,F,comp(Y,Z,Z,H,id(Z)))),comp(Z,X,Z,(comp(Z,Y,X,J,G)),K))=K)))) ).
