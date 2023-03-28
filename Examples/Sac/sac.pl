:- consult(interfaceCopy).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% SAC A DOS PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)).

% Prédicat pour résoudre le problème du sac à dos
knapsack(Ws, Vs, C, Xs, Value) :-
    length(Ws, N),
    length(Xs, N),
    Xs ins 0..1,
    scalar_product(Ws, Xs, #=<, C),
    scalar_product(Vs, Xs, #=, Value).

% Poids et valeurs des objets
weights([5, 3, 2, 1, 4, 6, 7, 15, 9, 7, 3, 4]).
values([60, 50, 70, 30, 50, 60, 80, 200, 100, 75, 65, 70]).
capacity(15).

% Trouver la solution avec la valeur maximale
solve(Xs, MaxValue) :-
    weights(Ws),
    values(Vs),
    capacity(C),
    findall((Value, Xs), (knapsack(Ws, Vs, C, Xs, Value), label(Xs)), Solutions),
    max_member((MaxValue, Xs), Solutions).

% Exemple d'exécution : ?- solve(Xs, MaxValue).




%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% SAC A DOS SMTLIB %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

sac_smtlib() :-
	smt_load_file('sac.smt2', [], Script),
	smt_solve_z3(Script,_).