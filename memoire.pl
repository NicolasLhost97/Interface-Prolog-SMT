:- consult(interface).
:- use_module(library(clpfd)).

queens(N):-
    smt_new_stream('Nqueens', Script),
    smt_cvc4_options(Script),
    queens_declaration(N, Script),
    queens_on_board(0, N, Script),
    queens_not_same_row(N, Script),
    smt_define_fun('diagonal-threat', 
        [['x1','Int'], ['y1','Int'], ['x2','Int'], ['y2','Int']], 'Bool',
        [=, [abs, [-, 'x1', 'x2']], [abs, [-, 'y1', 'y2']]], Script),
    queens_not_same_diagonal(N, 0, Script),
    smt_check_sat(Script),
    smt_get_model(Script),
    smt_solve_with_z3(Script),
    smt_close_stream(Script).


% Declaration of queens
queens_declaration(0, _).
queens_declaration(N, Script) :-
    succ(PrecN, N),
    atom_concat('r', PrecN, VarName),
    smt_declare_fun(VarName, [], 'Int', Script),
    queens_declaration(PrecN, Script).

% Rule to have queens inside the limits
queens_on_board(N, N, _).
queens_on_board(I, N, Script) :-
    atom_concat('r', I, VarName),
    smt_assert([and,[>=, VarName, 0],[<, VarName, N]], Script),
    succ(I, NextI),
    queens_on_board(NextI, N, Script).

% Rule to avoid queens in same row
queens_not_same_row(N, Script) :-
    succ(PrecN, N),
    findall(Queen, (between(0, PrecN, I), 
            atom_concat('r', I, Queen)), Queens),
    smt_assert([distinct | Queens], Script).

% Rule to avoid queens in same diagonal
queens_not_same_diagonal(N, I, _) :-
    I >= N. 
queens_not_same_diagonal(N, I, Script) :-
    I < N,
    JStart is I + 1,
    queens_not_same_diagonal_inner_loop(N, I, JStart, Script),
    I1 is I + 1,
    queens_not_same_diagonal(N, I1, Script).

queens_not_same_diagonal_inner_loop(N, _, J, _) :-
    J >= N.
queens_not_same_diagonal_inner_loop(N, I, J, Script) :-
    J < N,
    atom_concat('r', I, R1),
    atom_concat('r', J, R2),
    smt_assert([not, ['diagonal-threat', R1, I, R2, J]], Script),
    J1 is J + 1,
    queens_not_same_diagonal_inner_loop(N, I, J1, Script).




solve(N) :- 
    smt_new_stream('loop', Script),
    loop(N, Script),
    smt_solve_with_z3(Script),
    smt_close_stream(Script).

loop(0,_) :- !.
loop(N,Script) :-
    N > 0,
    smt_declare_const(x, 'Int', Script),
    N1 is N - 1,
    loop(N1, Script).
    
