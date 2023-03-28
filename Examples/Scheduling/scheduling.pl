:- consult(interfaceCopy).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% SCHEDULING PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)).

% Prédicat pour résoudre le problème de scheduling
scheduling(Ss, Es, Ds, TotalDuration) :-
    Ss = [S1, S2, S3],
    Es = [E1, E2, E3],
    Ds = [D1, D2, D3],
    E1 #= S1 + D1,
    E2 #= S2 + D2,
    E3 #= S3 + D3,
    (E1 #=< S2 #\/ E2 #=< S1),
    (E1 #=< S3 #\/ E3 #=< S1),
    (E2 #=< S3 #\/ E3 #=< S2),
    max_list(Es, TotalDuration).

% Durées des tâches
durations([3, 4, 2]).

% Trouver la solution avec la durée minimale
scheduling_prolog(Ss, Es, MinDuration) :-
    durations(Ds),
    scheduling(Ss, Es, Ds, TotalDuration),
    append(Ss, Es, Vars),
    append(Vars, [TotalDuration], AllVars),
    AllVars ins 0..1000,
    labeling([min(TotalDuration)], AllVars),
    MinDuration = TotalDuration.

max_list([X], X).
max_list([X|Xs], Max) :-
    max_list(Xs, TailMax),
    Max #= max(X, TailMax).

% Exemple d'exécution : ?- scheduling_prolog(Ss, Es, MinDuration).




%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% SCHEDULING SMTLIB %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%

scheduling_smtlib() :-
	smt_load_file('scheduling.smt2', [], Script),
	smt_solve_z3(Script,_).