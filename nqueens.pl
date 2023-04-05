:- consult(interfaceStream).
:- use_module(interfaceStream).
:- use_module(library(clpfd)).

queens(N):-
    smt_new('Nqueens', Script),
    queens_declaration(N, Script),
    queens_on_board(N, Script),
    queens_not_same_row(N, Script),
    smt_define_fun('diagonal-threat', [['x1','Int'], ['y1','Int'], ['x2','Int'], ['y2','Int']], 'Bool',
            [=, [abs, [-, 'x1', 'x2']], [abs, [-, 'y1', 'y2']]], Script),
    queens_not_same_diagonal(N, 0, Script),
    smt_check_sat(Script),
    smt_get_model(Script),
    smt_solve_z3(Script),
    queens_get_solution(Script, N, 0, AllValues),
    print_board(AllValues).


    queens_declaration(N, Script) :-
        succ(PrecN, N),
        forall(between(0, PrecN, I),
            (   atom_concat('r', I, VarName),
                smt_declare_fun(VarName, [], 'Int', Script)
            )
        ).
    
    queens_on_board(N, Script) :-
        succ(PrecN, N),
        forall(between(0, PrecN, I),
            (   atom_concat('r', I, VarName),
                smt_assert([and,[>=, VarName, 0],[<, VarName, N]], Script)
            )
        ).

    queens_not_same_row(N, Script) :-
        succ(PrecN, N),
        findall(Queen, (between(0, PrecN, I), atom_concat('r', I, Queen)), Queens),
        smt_assert([distinct | Queens], Script).


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


    queens_get_solution(_, N, N, []).
    queens_get_solution(Script, N, I, [Value | Rest]) :-
        I < N,
        atom_concat('r', I, Var),
        smt_get_last_model_value(Var, Value, Script),
        I1 is I + 1,
        queens_get_solution(Script, N, I1, Rest).
        

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