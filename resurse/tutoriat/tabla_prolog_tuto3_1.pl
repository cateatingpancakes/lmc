:- [lab7lmc2].
:- set_prolog_flag(answer_write_options, [max_depth(0)]). % scrie listele complet

% Exemplu pentru examen:
% l4(-L4, -OrdL4)
l4(L4, OrdL4) :- L4 = [0, a, b, 1],
                 orddinsucc([(0, a), (a, b), (b, 1)], L4, OrdL4).

% l2xl3(-L2xL3, -OrdL2xL3)
l2xl3(L2xL3, OrdL2xL3) :- L2xL3 = [0, a, b, c, d, 1],
                          orddinsucc([(0, a), (0, b), (a, c), (b, c), (b, d), (c, 1), (d, 1)], L2xL3, OrdL2xL3).

% fctstrcrescaux(+P, +OrdP, +Q, +OrdQ, -LF)
fctstrcrescaux(P, OrdP, Q, OrdQ, LF) :- setof(F, fctstrcresc(F, P, OrdP, Q, OrdQ), LF).

% fctL2xL3laL4(-LF)
fctL2xL3laL4(LF) :- l4(L4, OrdL4), l2xl3(L2xL3, OrdL2xL3),
                    fctstrcrescaux(L2xL3, OrdL2xL3, L4, OrdL4, LF).

% daca uitam, nu e foarte dificil sa scriem singuri:
% estesurjectiva(+F, +Codom)
% estesurjectiva(F, Codom) :- not((member((_, Y), F),
%                                not(member(Y, Codom)))).

niciunasurjaux(LF, Codom) :- not((member(F, LF),         % Nu exista niciun F din lista LF de funcii
                                  surjectiv(F, Codom))). % pentru care surjectiv(F, Codom).
                                                         % => nu exista functii surjective.

% niciunasurj/0
niciunasurj :- l4(L4, _), fctL2xL3laL4(LF),
               niciunasurjaux(LF, L4).


% niciunamorflataux(+LF, +P, +OrdP, +Q, +OrdQ)
niciunamorflataux(LF, P, OrdP, Q, OrdQ) :- not((member(F, LF),                  % Nu exista niciun F din lista LF de functii (member)
                                                morflat(F, P, OrdP, Q, OrdQ))). % pentru care morflat(F, ...)
                                                                                % => nu exista morfisme de latici

% niciunamorflat/0
niciunamorflat :- l4(L4, OrdL4), l2xl3(L2xL3, OrdL2xL3), fctL2xL3laL4(LF),
                  not((member(F, LF),
                       morflat(F, L2xL3, OrdL2xL3, L4, OrdL4))), !.

% setof(+F, Conditie, -LF)
% not(( ... )) => "nu exista"

% Recapitulare lab. 1-3 pentru TC #1
% A ∆ B = (A ∪ B) \ (A ∩ B)
xor(P, Q) :- P, not(Q); Q, not(P).
% A \ B
minus(P, Q) :- P, not(Q).

% _a => elementul apartine multimii A
% _b => elementul apartine multimii B
% dedem(+_a, +_b)
dedem(_a, _b) :- echiv(xor(_a, _b), minus((_a; _b), (_a, _b))).

% dem/0 => va fi true, daca afirmatia pe care
% vreau sa o demonstrez este adevarata

dem :- not((listaValBool([_a, _b]), % nu exista o lista de val. bool. [_a, _b],
            not(dedem(_a, _b)))).   % pentru care sa nu aiba loc ceea ce aveam dedem.
                                    % => nu exista contraexemplu => e adevarat