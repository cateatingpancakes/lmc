:- [lab7lmc2].

% neg(a, b) inseamna ca simbolul a negat este simbolul b
% Folosim acest predicat ca sa putem lucra mai departe, not(a) nu merge.
neg(a, na).
neg(b, nb).
neg(d, nd).
neg(e, ne).
neg(g, ng).
neg(na, a).
neg(nb, b).
neg(nd, d).
neg(ne, e).
neg(ng, g).

% Multimea sigma la exemplul explicat din tutoriatul 4 cu Davis-Putnam, vezi GitHub
sigmaexemplu(Sigma) :- Sigma = [[a, nb], [a, d, e], [na, nd], [na, g], [b, g]].


cusimbol(Sigma, Simbol, Filtrat) :- setof(Clauza,                      % ia toate variabilele Clauza
                                            (member(Clauza, Sigma),    % care este member al Sigma
                                             member(Simbol, Clauza)),  % si care are Simbol ca member
                                          Filtrat),                    % si colecteaza-le in Filtrat
                                          !.


reuniunile(M1, M2, M) :- findall(LR,                % fie un LR asa incat daca
                            (member(L1, M1),        % iei o multime L1 din M1 si
                             member(L2, M2),        % iei o multime L2 din M2
                             reuniune(L1, L2, LR)), % reuniunea L1 cu L2 da LR
                            M).                     % afla toti acesti LR si colecteaza-i in M
                                                    %   ("find all")


% predicatul maplist
elimsim(Simbol, LM, LMfaraSimbol) :- maplist(stergesimbol(Simbol), LM, LMfaraSimbol).
% predicatul delete
stergesimbol(Simbol, M, MfaraSimbol) :- delete(M, Simbol, MfaraSimbol).

                                        % o clauza are pozitiv-cu-negativ daca pot sa iau din ea:
pozcuneg(Clauza) :- member(P, Clauza),  % un member P,
                    member(Q, Clauza),  % un member Q,
                    neg(P, Q),          % si neg(P, Q) are loc,
                    !.                  % si e suficient sa gasesti doar un exemplu.


elimpozcuneg(Sigma, Filtrat) :- setof(Clauza, (member(Clauza, Sigma),
                                               not(pozcuneg(Clauza))), Filtrat).

% Nu e perfect, dar luati-l ca exemplu, demonstrativ!
% Se poate mai eficient, mai sunt deduplicari de facut                                          
eliminaredavisputnam(Sigma, VarElim, SigmaUrm) :-
    neg(VarElim, NonVarElim),                       % obtine simbolul pentru negatia variabilei de eliminat
    cusimbol(Sigma, VarElim, CuV),                  % clauzele cu VarElim
    cusimbol(Sigma, NonVarElim, CuNV),              % cu negatia lui VarElim
    diferenta(Sigma, CuV, FaraV),                   % care nu au nici una nici alta
    diferenta(FaraV, CuNV, FaraVsiNV),              % (obtinut in 2 pasi, 2 apeluri predicat laborator)
    elimsim(VarElim, CuV, CuVscos),                 % elimina simbolul VarElim
    elimsim(NonVarElim, CuNV, CuNVscos),            % si simbolul NonVarElim
    reuniunile(CuVscos, CuNVscos, Combinat),        % combina multimile
    elimpozcuneg(Combinat, CombinatPN),             % elimina cele unde apare orice simbol si pozitiv si negativ
    elimdupl(CombinatPN, CombinatPNsiDD),           % elimina duplicatele daca apar la nivel de clauze
    append(FaraVsiNV, CombinatPNsiDD, SigmaUrm),    % alatura ce nu a intrat in eliminare cu rezultatul de dupa ea
    !.                                              

rezolutiedavisputnam(Sigma, [], Sigma).
rezolutiedavisputnam(Sigma, [H|T], SigmaRez) :- eliminaredavisputnam(Sigma, H, SigmaUrm),
                                                rezolutiedavisputnam(SigmaUrm, T, SigmaRez).

satisfiabildavisputnam(Sigma, Variabile) :- not(rezolutiedavisputnam(Sigma, Variabile, _)).

% Mod apel:
% ?- sigmaexemplu(Sigma), eliminaredavisputnam(Sigma, a, SigmaUrm).
% ?- sigmaexemplu(Sigma), rezolutiedavisputnam(Sigma, [a,b,d,e,g], SigmaUrm).