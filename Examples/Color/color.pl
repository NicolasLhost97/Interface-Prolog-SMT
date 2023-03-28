:- consult(interfaceCopy).
:- use_module(library(clpfd)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% COLOR GRAPH PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Définir le graphe avec des arêtes (i, j)
graph([(0,1), (1,3), (2,3), (3,0), (0,4), (1,5), (2,6), (3,7), (4,5), (5,6), (6,7), (7,4), (4,8), (5,9), (6,10), (7,11), (8,9), (9,10), (10,11), (11,8), (8,12), (9,13), (10,14), (11,15), (12,13), (13,14), (14,15), (15,12)]).

% Contraintes de coloration pour une paire de sommets (i, j)
color_constraint(Colors, I, J) :-
    nth0(I, Colors, ColorI),
    nth0(J, Colors, ColorJ),
    ColorI #\= ColorJ.

% Appliquer les contraintes de coloration à toutes les arêtes
apply_color_constraints(_, []).
apply_color_constraints(Colors, [(I, J) | Rest]) :-
    color_constraint(Colors, I, J),
    apply_color_constraints(Colors, Rest).

color_graph_prolog(N, K, Colors) :-
    length(Colors, N),
    Colors ins 1..K,
    graph(Edges),
    apply_color_constraints(Colors, Edges),
    label(Colors).

% Afficher les couleurs de chaque sommet
print_colors(_, []).
print_colors(Index, [Color | Rest]) :-
    format("Sommet ~w: Couleur ~w~n", [Index, Color]),
    NewIndex is Index + 1,
    print_colors(NewIndex, Rest).

% Exemple d'utilisation avec color_graph_prolog
% ?- color_graph_prolog(16, 4, Colors), print_colors(0, Colors).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% COLOR GRAPH SMT %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

color_graph_smtlib() :-
	smt_load_file('color.smt2', [], Script),
	smt_solve_cvc4(Script,_).