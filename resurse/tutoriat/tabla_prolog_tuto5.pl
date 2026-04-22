:- [lab7lmc2].

% A ∪ B                  -> (A; B)
% A ∩ B                  -> (A, B)
% A ∆ B                  -> xor(A, B)
% A ⊆ B                  -> implica(A, B)
% A \ B                  -> dif(A, B)
% A barat                -> not(A)
% ∅                      -> False
% A ⊆ taiat B            -> not(implica(A, B))
% A inclus dar nu egal B -> implica(A, B), not(implica(B, A)) / inclnuegal(A, B)
% A ⇔ B                  -> echiv(A, B)

dif(A, B) :- A, not(B).
inclnuegal(A, B) :- implica(A, B), not(implica(B, A)).

% A ∪ A = A
stg1(_a) :- _a; _a.
dre1(_a) :- _a.
echivstgcudr1(_a) :- echiv(stg1(_a), dre1(_a)).


suntechiv1stgcudr :- not((listaValBool([_a]),
                          not(echivstgcudr1(_a)))).

% A ⊆ B ⇒ ((A \ C) ⊆ (B \ C) si (C \ B) ⊆ (C \ A))
stg2(_a, _b, _c) :- implica(_a, _b).
dre2(_a, _b, _c) :- (implica(dif(_a, _c), dif(_b, _c)), implica(dif(_c, _b), dif(_c, _a))).

echivstgcudr2(_a, _b, _c) :- echiv(stg2(_a, _b, _c), dre2(_a, _b, _c)).

suntechiv2stgcudr :- not((listaValBool([_a, _b, _c]),       % Nu exista o lista de valori booleene [_a, _b, _c]
                          not(echivstgcudr2(_a, _b, _c)))). % pentru care nu are loc echivalenta ceruta =>
                                                            % => Are loc mereu

% A ⊆ B ⇔ (A inclus dar nu egal B sau A = B)
stg3(_a, _b) :- implica(_a, _b).
dre3(_a, _b) :- (inclnuegal(_a, _b); echiv(_a, _b)).

echivstgcudr3(_a, _b) :- echiv(stg3(_a, _b), dre3(_a, _b)).

suntechiv3stgcudr :- not((listaValBool([_a, _b]),
                          not(echivstgcudr3(_a, _b)))).