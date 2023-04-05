:- consult(interfaceCopy).
:- use_module(library(clpfd)).

%%%%%%%%%%%%%%%%%%%%%%%
%%%% NQUEEN PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%

nqueens_prolog(N) :-
    length(Queens, N),
	board(Queens, Board, 0, N, _, _),
	nqueens_prolog(Board, 0, Queens),
	print_board(Queens).

board([], [], N, N, _, _).
board([_|Queens], [Col-Vars|Board], Col0, N, [_|VR], VC) :-
	Col is Col0+1,
	functor(Vars, f, N),
	constraints(N, Vars, VR, VC),
	board(Queens, Board, Col, N, VR, [_|VC]).

constraints(0, _, _, _) :- !.
constraints(N, Row, [R|Rs], [C|Cs]) :-
	arg(N, Row, R-C),
	M is N-1,
	constraints(M, Row, Rs, Cs).

nqueens_prolog([], _, []).
nqueens_prolog([C|Cs], Row0, [Col|Solution]) :-
	Row is Row0+1,
	select(Col-Vars, [C|Cs], Board),
	arg(Row, Vars, Row-Row),
	nqueens_prolog(Board, Row, Solution).

print_board(Rows) :-
	length(Rows, N),
	print_board_helper(Rows, N, 0).

print_board_helper(_, N, N) :-
	nl.
print_board_helper(Rows, N, Row) :-
	print_row(Rows, N, Row, 0),
	nl,
	NextRow is Row + 1,
	print_board_helper(Rows, N, NextRow).

print_row(_, N, _, N).
print_row(Rows, N, Row, Col) :-
	nth0(Row, Rows, QueenCol),
	(QueenCol =:= Col -> write('Q ') ; write('. ')),
	NextCol is Col + 1,
	print_row(Rows, N, Row, NextCol).

% Exemple d'utilisation :
% ?- nqueens_prolog(8, Q).


%%%%%%%%%%%%%%%%%%%%%%%
%%%% NQUEEN SMTLIB %%%%
%%%%%%%%%%%%%%%%%%%%%%%

nqueens_smtlib() :-
	smt_load_file('nqueens.smt2', [], Script),
	smt_solve_z3(Script,_).

% Exemple d'utilisation :
% ?- queens_prolog(8).
