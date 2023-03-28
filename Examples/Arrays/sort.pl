:- use_module(library(clpfd)).
:- consult(interfaceCopy).

min_element([X], X).
min_element([H|T], Min) :-
    min_element(T, Tmin),
    Min #= min(H, Tmin).

remove(_, [], []).
remove(X, [X|T], T).
remove(X, [H|T], [H|R]) :-
    X #\= H,
    remove(X, T, R).

sort_prolog([], []).
sort_prolog(L, [Min|S]) :-
    min_element(L, Min),
    remove(Min, L, R),
    sort_prolog(R, S).

% Exemple d'exécution :
% ?- sort_prolog([4, 1, 3, 2], Sorted).


sort_smtlib():-
    smt_load_file('sorted.smt2', [], Script),
    smt_solve_cvc4(Script,_).