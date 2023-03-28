:- use_module(library(smtlib)).
:- use_module(library(clpfd)).

solve_sudoku(Board) :-
    length(Board, 9),
    maplist(length_(9), Board),
    smtlib_read_script('smt/sudoku.smt',Values),
    assign_values(Values, Board),
    maplist(writeln, Board).

assign_values([], _).
assign_values([Var = Val|Values], Board) :-
    get_variable_position(Var, Row, Col),
    nth0(Row, Board, RowList),
    nth0(Col, RowList, Val),
    assign_values(Values, Board).

length_(N, List) :- length(List, N).

get_variable_position(Var, Row, Col) :-
    sub_atom(Var, 1, _, 0, C),
    sub_atom(Var, _, 1, 0, R),
    atom_number(C, Col),
    atom_number(R, Row).
