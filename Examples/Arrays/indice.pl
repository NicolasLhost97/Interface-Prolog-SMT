% Prédicat pour vérifier si un élément est à un certain indice dans une liste
element_at(X, [X|_], 0).
element_at(X, [_|T], N) :- N > 0, N1 is N - 1, element_at(X, T, N1).

% Prédicat pour vérifier si A[i] + A[j] = k
find_indices(A, K, I, J) :-
    length(A, N),
    N >= 2,
    K >= 0,
    between(0, N - 1, I),
    between(0, N - 1, J),
    I =\= J,
    element_at(AI, A, I),
    element_at(AJ, A, J),
    K is AI + AJ.


:- use_module(library(clpfd)).

nonlinear_constraints(X, Y, Z) :-
    X in 0..10000000000,
    Y in 0..10000000000,
    Z in 0..10000000000,
    X + Y #= 10,
    Z #>= 25,
    findall((X, Y, Z), (label([X, Y]), Z #= X * Y), Solutions),
    member((X, Y, Z), Solutions),
    label([Z]).

