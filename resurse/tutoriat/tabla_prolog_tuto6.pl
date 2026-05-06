:- [lab7lmc2].

laticeA(A, OrdA) :- A = [0, a, b, c, 1], orddinsucc([(0, a), (0, b), (a, 1), (b, c), (c, 1)], A, OrdA).

laticeB(B, OrdB) :- B = [0, x, y, 1], orddinsucc([(0, x), (x, y), (y, 1)], B, OrdB).

toatefsc(A, OrdA, B, OrdB, LF) :- setof(F,
                                        fctstrcresc(F, A, OrdA, B, OrdB),
                                        LF).

cer1(LF) :- laticeA(A, OrdA), laticeB(B, OrdB), toatefsc(A, OrdA, B, OrdB, LF).

cer2 :- cer1(LF), laticeA(A, OrdA), laticeB(B, OrdB),
        not((
            member(F, LF),
            morflat(F, A, OrdA, B, OrdB)
        )), 
        !.