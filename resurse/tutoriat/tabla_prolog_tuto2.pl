:- [lab7lmc2].

% numere pare:
even(N):- mod(N, 2) =:= 0.
% elempare(+L, -LP)
% functionarea lui setof in Prolog:
elempare(L, LP) :- setof(E, (member(E, L), even(E)), LP).

% morfM3laL2(-LM)
morfM3laL2(LM) :- m3(R1, OrdR1), l2(R2, OrdR2), setof(F, morflat(F, R1, OrdR1, R2, OrdR2), LM), !.
