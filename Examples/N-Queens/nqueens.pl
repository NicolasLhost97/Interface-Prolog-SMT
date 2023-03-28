:- consult(interfaceCopy).
:- use_module(library(clpfd)).

%%%%%%%%%%%%%%%%%%%%%%%
%%%% NQUEEN PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%

nqueens_prolog(N, Queens) :-
    length(Queens, N),
	board(Queens, Board, 0, N, _, _),
	nqueens_prolog(Board, 0, Queens).

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
