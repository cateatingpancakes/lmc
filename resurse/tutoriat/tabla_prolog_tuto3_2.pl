:- [lab7lmc2].
:- set_prolog_flag(answer_write_options, [max_depth(0)]). 

% l4(-L4. -OrdL4)
l4(L4, OrdL4) :- L4 = [0, a, b, 1],
                 orddinsucc([(0, a), (a, b), (b, 1)], L4, OrdL4).

% l2xl2xl2(-Cub, -OrdCub)
l2xl2xl2(Cub, OrdCub) :- Cub = [0, a, b, c, x, y, z, 1],
                         orddinsucc([(0, a), (0, b), (0, c), (a, x), (a, y), (b, x), (b, z), (c, y), (c, z), (x, 1), (y, 1), (z, 1)], Cub, OrdCub).

fctstrcrescaux(P, OrdP, Q, OrdQ, LF) :- setof(F, fctstrcresc(F, P, OrdP, Q, OrdQ), LF).

fctL4laL2xL2xL2(LF) :- l4(L4, OrdL4), l2xl2xl2(Cub, OrdCub), 
                       fctstrcrescaux(L4, OrdL4, Cub, OrdCub, LF).

toatemorflatmargaux(LF, P, OrdP, Q, OrdQ) :- not((member(F, LF),                            % nu exista nicio functie F din lista LF de functii
                                                  not(morflatmarg(F, P, OrdP, Q, OrdQ)))).  % pentru care not(morflatmarg(F, ...))
                                                                                            % => toate sunt morflatmarg

% toatemorflatmarg/0
toatemorflatmarg :- l4(L4, OrdL4), l2xl2xl2(Cub, OrdCub), fctL4laL2xL2xL2(LF),
                    toatemorflatmargaux(LF, L4, OrdL4, Cub, OrdCub), !.