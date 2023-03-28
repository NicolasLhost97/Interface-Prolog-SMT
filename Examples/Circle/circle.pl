:- use_module(library(clpfd)).
:- use_module(library(clpr)).

circle_intersection(X1, Y1, R1, X2, Y2, R2, X, Y) :-
    X in -1000..1000,
    Y in -1000..1000,
    indomain(X),
    indomain(Y),
    { (X - X1) * (X - X1) + (Y - Y1) * (Y - Y1) =:= R1 * R1 },
    { (X - X2) * (X - X2) + (Y - Y2) * (Y - Y2) =:= R2 * R2 }.

main :-
    X1 = 1,
    Y1 = 2,
    R1 = 2,
    X2 = 4,
    Y2 = 2,
    R2 = 1,
    circle_intersection(X1, Y1, R1, X2, Y2, R2, X, Y),
    format("Intersection: (~3f, ~3f)~n", [X, Y]),
    halt.


