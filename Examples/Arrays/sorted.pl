:- use_module(library(clpfd)).
:- consult(interfaceCopy).

% Prédicat pour vérifier si un tableau est trié
is_sorted_prolog([]).
is_sorted_prolog([_]).
is_sorted_prolog([A, B | Tail]) :-
    A #=< B,
    is_sorted_prolog([B | Tail]).

% Exemple d'exécution:
% ?- is_sorted([X1, X2, X3, X4]).
%[3,7,9,15,18,22,25,29,32,35]

is_sorted_smt():-
    smt_load_file('sorted.smt2', [], Script),
    smt_solve_z3(Script,_).