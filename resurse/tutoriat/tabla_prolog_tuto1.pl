:- [lab7lmc2].

% Fibonacci recursiv
% fib(+N, -V)
% Asta inseamna ca "fib" ia ca input N si produce V
% In limbaj natural, propozitia "fib(N, V)." se traduce 
% "A N-a valoare a sirului lui Fibonacci este V."

fib(0, 0).
fib(1, 1).
fib(N, V) :- PN is N - 1, PPN is N - 2, fib(PN, V1), fib(PPN, V2), V is V1 + V2.

% Un exemplu de exercitiu de examen in Prolog.
% Predicatele implica, echiv ar trebui sa fie in [lab7lmc2].

implica(A, B) :- not(A); B.
echiv(A, B) :- implica(A, B), implica(B, A).

% ipoteza1, ipoteza2, concluzia(+Alfa, +Beta, +Gama)
% Asa ni s-a cerut la examen sa facem predicatele,
% asa implementam.

ipoteza1(Alfa, Beta, Gama) :- implica(Alfa, (Beta; Gama)).
ipoteza2(Alfa, Beta, Gama) :- echiv((Alfa; Beta), implica(Gama, Alfa)).
concluzia(Alfa, Beta, Gama) :- Alfa; Beta; Gama.

% Putem scrie si "desfasurat" in Prolog.

dem :- not((listaValBool([Alfa, Beta, Gama]),   % Nu exista o lista de valori booleene Alfa, Beta, Gama,
            ipoteza1(Alfa, Beta, Gama),         % Care sa respecte ipoteza 1,
            ipoteza2(Alfa, Beta, Gama),         % Si care sa respecte si ipoteza 2,
            not(concluzia(Alfa, Beta, Gama)))). % Si sa nu se indeplineasca concluzia
                                                % => propozitia este adevarata.

% Suma elementelor dintr-o lista.
% sumelem(+L, -S)
% ^^^. De ce?

sumelem([], 0).
sumelem([H], H).
sumelem([H|T], S) :- sumelem(T, ST), S is H + ST.

% Inversare lista in Prolog.

invlista([], []).
invlista([H|T], IL) :- invlista(T, IT), append(IT, [H], IL). 

% Toate elementele mai mici ca un K dat.
% maimici(+L, +K, -MM)

maimici([], _, []).
maimici([H|T], K, MM) :- H > K, maimici(T, K, MM).
maimici([H|T], K, [H|MM]) :- maimici(T, K, MM).

% Analog se face pentru mai mari ca un K dat.

maimari([], _, []).
maimari([H|T], K, MM) :- H < K, maimari(T, K, MM).
maimari([H|T], K, [H|MM]) :- maimari(T, K, MM).

% Cu astfel de predicate pot sa implementez quicksort!
% Nu e un QS foarte eficient, dar va da rezultat corect.

qsort([], []).
qsort([H], [H]).
qsort([H|T], LS) :- maimici(T, H, MaiMici), 
                    qsort(MaiMici, MaiMiciS),
                    maimari(T, H, MaiMari), 
                    qsort(MaiMari, MaiMariS), 
                    append(MaiMiciS, [H], LS1), 
                    append(LS1, MaiMariS, LS).
