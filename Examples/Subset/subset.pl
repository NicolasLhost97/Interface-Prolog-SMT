:- use_module(library(clpfd)).

subseq([], []).
subseq([X|Xs], [X|Ys]) :- subseq(Xs, Ys).
subseq([_|Xs], Ys) :- subseq(Xs, Ys).

subset_sum(Values, Solution, Target) :-
    subseq(Values, Solution),
    sum(Solution, #=, Target).

sum([], 0).
sum([X|Xs], Total) :- sum(Xs, SubTotal), Total #= X + SubTotal.

main :-
    Values = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 16, 20, 24, 30, 32, 40],
    Target = 18,
    subset_sum(Values, Solution, Target),
    format("Solution: ~w~n", [Solution]). 
