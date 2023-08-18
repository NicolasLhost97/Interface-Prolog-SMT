:- consult(interface).
:- use_module(library(clpfd)).

queens(N):-
    smt_new_stream('Nqueens', Script),
    queens_declaration(N, Script),
    queens_on_board(0, N, Script),
    queens_not_same_row(N, Script),
    smt_define_fun('diagonal-threat', [['x1','Int'], ['y1','Int'], ['x2','Int'], ['y2','Int']], 'Bool',
            [=, [abs, [-, 'x1', 'x2']], [abs, [-, 'y1', 'y2']]], Script),
    queens_not_same_diagonal(N, 0, Script),
    smt_check_sat(Script),
    smt_get_model(Script),
    smt_solve_with_z3(Script),
    queens_get_solution(Script, N, 0, AllValues),
    valid_solution(AllValues, N),
    print_board(AllValues),
    smt_close_stream(Script).


queensAllSolutions(N):-
    smt_new_stream('NqueensAllSolution', Script),
    queens_declaration(N, Script),
    queens_on_board(0, N, Script),
    queens_not_same_row(N, Script),
    smt_define_fun('diagonal-threat', [['x1','Int'], ['y1','Int'], ['x2','Int'], ['y2','Int']], 'Bool',
            [=, [abs, [-, 'x1', 'x2']], [abs, [-, 'y1', 'y2']]], Script),
    queens_not_same_diagonal(N, 0, Script),
    allrows(N, Rows),
    getAllSolutions(Script, N, Rows, [], Solutions),
    writeAllSolutions(Solutions),
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
        findall(Queen, (between(0, PrecN, I), atom_concat('r', I, Queen)), Queens),
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

    %Retrieve the solution in an array
    queens_get_solution(_, N, N, []).
    queens_get_solution(Script, N, I, [Value | Rest]) :-
        I < N,
        atom_concat('r', I, Var),
        smt_get_last_model_value(Var, Value, Script),
        I1 is I + 1,
        queens_get_solution(Script, N, I1, Rest).

    %Check if the solution is valid
    valid_solution(Queens, N) :-
        length(Queens, N),
        on_board(Queens, N),
        valid_rows(Queens),
        valid_diagonals(Queens).

        on_board([], _).
        on_board([Q | Rest], N) :-
            Q >= 0,
            Q < N,
            on_board(Rest, N).
    
        valid_rows(Queens) :-
            sort(Queens, Sorted),
            length(Queens, Len),
            length(Sorted, Len).
        
        valid_diagonals([]).
        valid_diagonals([Q | Rest]) :-
            valid_diagonal(Q, Rest, 1),
            valid_diagonals(Rest).
        
        valid_diagonal(_, [], _).
        valid_diagonal(Q, [R | Rest], Dist) :-
            Diff is abs(Q - R),
            Diff =\= Dist,
            NewDist is Dist + 1,
            valid_diagonal(Q, Rest, NewDist).

    
    % Loop until all solutions are found
    getAllSolutions(Script, _, _, Solutions, Solutions) :-
        \+ smt_check_sat_continue_if_sat(Script).
    getAllSolutions(Script, N, Rows, Acc, Solutions) :-
        smt_check_sat_continue_if_sat(Script),
        smt_get_model_to_constraint_for(Rows, Script),
        (smt_solve_with_z3(Script) ->
            (queens_get_solution(Script, N, 0, Solution),
            valid_solution(Solution, N),
            getAllSolutions(Script, N, Rows, [Solution | Acc], Solutions))
        ;
            Solutions = Acc
        ).

    % List all N rows    
    allrows(N, Rows) :-
        succ(PrecN,N),
        numlist(0, PrecN, NumList),
        maplist(row_var, NumList, Rows).
    row_var(N, RowVar) :-
        atom_concat('r', N, RowVar).
                
    % Write all solutions
    writeAllSolutions([]).
    writeAllSolutions([Solution | Rest]) :-
        writeln(Solution),
        print_board(Solution),
        writeAllSolutions(Rest).
        
      
    %Print the board
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







%%%%%%%%%%%%%%%%%%%%%%%
%%%% NQUEEN PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%

n_queens(N, Qs) :-
    length(Qs, N),
    Qs ins 1..N,
    safe_queens(Qs).

safe_queens([]).
safe_queens([Q|Qs]) :- safe_queens(Qs, Q, 1), safe_queens(Qs).

safe_queens([], _, _).
safe_queens([Q|Qs], Q0, D0) :-
    Q0 #\= Q,
    abs(Q0 - Q) #\= D0,
    D1 #= D0 + 1,
    safe_queens(Qs, Q0, D1).