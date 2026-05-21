:- [lab7lmc2].
:- set_prolog_flag(answer_write_options, [max_depth(0)]). 

% ϕ = (α → β) → (α ∧ ¬ β).

fi(A, B) :- implica(implica(A, B), (A, not(B))).

propr1 :- listaValBool([A, B]), fi(A, B), !.

propr2 :- not((listaValBool([A, B]),    % nu exista LVB/intepretatre
               fi(A, B),                % astfel incat sa fim in conditiile ipotezei
                                        % si sa fie si multimea {A, B} satisfacuta:
               A,                       % adica sa aiba loc A din {A, B}
               B                        % si sa aiba loc si B din {A, B}
               )).

% 

detA(A) :- A = [a, b, c, d].

rs(Succ) :- Succ = [(a, b), (b, c), (c, d)].

detF(F) :- detA(A), functie(F, A, A), inchrefl(F, A, IRF), rs(Succ), inchrefl(Succ, A, IRS), egalmult(IRF, IRS), !.

detR(R) :- ordstrdinsucc([(a, b), (a, c), (b, d), (c, d)], R), !.

detK(K) :- detF(F), detR(R), intersectie(F, R, IFR), member((K, _), IFR), member(K, [b, c, d]), !.


% important!
listaValMult(_, []).
listaValMult(M, [H|T]) :- member(H, M), listaValMult(M, T).

listaValMultWrite(M, L) :- listaValMult(M, L), write(L), nl.

verifAsatepsilon :- detA(A), detF(F), detR(R), detK(K),
                    not((
                        listaValMult(A, [X, Y]), % nu exista o lista de valori din multimea A, [X, Y]
                        not(                     % asa incat sa nu aiba loc ceea ce era de demonstrat
                            implica(
                                (
                                    member( (X, K), F ),
                                    member( (K, Y), F ),
                                    member( (K, Y), R )
                                ),
                                member( (X, Y), R )
                            )
                        )
                    )).

% Latici

l4(L, OrdL) :- L = [0, a, b, 1], orddinsucc([(0, a), (a, b), (b, 1)], L, OrdL), !.

fctstrcresclat(P, OrdP, Q, OrdQ, LF) :- setof(F, (functie(F, P, Q), fctstrcresc(F, P, OrdP, Q, OrdQ)), LF), !.

fctL4laL2xL2xL2(LF) :- l4(L, OrdL), cub(C, OrdC), fctstrcresclat(L, OrdL, C, OrdC, LF), !.

toatemorflatmarg :- l4(L, OrdL), cub(C, OrdC), fctL4laL2xL2xL2(LF),
                    not((
                        member(F, LF),                          % nu exista membru F al listei de functii F
                        not(
                            morflatmarg(F, L, OrdL, C, OrdC)    % si care nu e morfism de latici marginite
                        )
                    )), !.