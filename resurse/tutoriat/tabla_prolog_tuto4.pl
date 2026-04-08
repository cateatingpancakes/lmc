:- [lab7lmc2].

% Nu e strict necesar, dar poate va ajuta sa ne scriem separat enunturile
% In plus, poate nu stim tot subiectul dar primim partial pe implementarea aceasta
enunt1(Alfa, Beta, Gama) :- implica(not(Alfa), (Beta, Gama)).
enunt2(Alfa, Beta, Gama) :- echiv(Alfa, (Beta; Gama)).

% LB = o lista de valori booleene (= o interpretare)
% LS = o lista de interpretari in care sigma e satisfacut
satisfSigmaAux(LS) :- setof(LB,                             % genereaza LB-uri
                                (LB = [Alfa, Beta, Gama],   % care unifica cu lista de 3 elemente [Alfa, Beta, Gama]
                                 listaValBool(LB),          % care este o lista de valori booelene
                                 enunt1(Alfa, Beta, Gama),  % si pentru care are loc enunt1
                                 enunt2(Alfa, Beta, Gama)), % si pentru care are loc enunt2
                            LS).                            % si colecteaza toate LB-urile acestea intr-o lista LS


% Se putea face si altfel, dar am vrut sa vedem si care sunt interpretarile,
% nu doar sa verificam ca este sigma satisfiabil (le aflam pe toate, nu doar una).
satisfSigma :- satisfSigmaAux(LS), 
               not(length(LS, 0)), 
               !.   % Utilitatea lui ! => Am 3 interpretari in care sigma e satisfacut, deci apar 3 de "true"
                    % Ganditi-va daca am mai multe variabile/interpretari valide
                    % Daca nu dadeam cut, trebuia sa ii vad pe toti