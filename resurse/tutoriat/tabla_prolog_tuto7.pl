:- [lab7lmc2].

% PROBLEMA 1

ipoteza1(Alfa, Beta, Gama) :- implica(not(Alfa), echiv(Beta, not(Gama))).

ipoteza2(Alfa, Beta, Gama) :- echiv((Alfa, Beta), (Beta, Gama)).

concluzia(Alfa, Beta, Gama) :- implica((Beta, Gama), Alfa).

deductie :- not((listaValBool([Alfa, Beta, Gama]), % Nu exista lista de valori booleene [Alfa, Beta, Gama]
                 ipoteza1(Alfa, Beta, Gama),       % Asa incat sa aiba loc ipoteza1
                 ipoteza2(Alfa, Beta, Gama),       % Si sa aiba loc si ipoteza2
                 not(concluzia(Alfa, Beta, Gama))  % Si cumva sa nu aiba loc concluzia
                 )).


% PROBLEMA 2

fiprob2(Alfa, Beta) :- implica(implica(Alfa, Beta), echiv(Alfa, Beta)).

cond(Alfa, Beta) :- not(Alfa), Beta.

fisatisf :- listaValBool([Alfa, Beta]), fiprob2(Alfa, Beta), !.

finesatisf :- not((listaValBool([Alfa, Beta]),
                   cond(Alfa, Beta),
                   fiprob2(Alfa, Beta)
                )).

% PROBLEMA 3

fiprob3(Alfa, Beta) :- echiv(implica(Alfa, Beta), implica((Alfa; Beta), (Alfa, Beta))).

psiprob3(Alfa, Beta) :- implica(Beta, Alfa).

echivsemfipsi(Alfa, Beta) :- echiv(fiprob3(Alfa, Beta), psiprob3(Alfa, Beta)).

echivsem :- not((listaValBool([Alfa, Beta]),
                 not(echivsemfipsi(Alfa, Beta))
                )).