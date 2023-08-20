:- consult(interface). % Load the interface

% Test all SMT-LIBv2 Script's commands
check_parsing :-
    smt_new_stream('checkAllParsing',Script),
    % Générer les commandes SMT-LIB
    smt_set_info(status, unknown, Script),
    smt_set_option(interactive-mode, true, Script),
    smt_set_option(produce-proofs, true, Script),
    smt_set_option(produce-unsat-cores, true, Script),
    smt_set_option(produce-unsat-assumptions, true, Script),
    smt_set_option(print-success, true, Script),
    smt_declare_sort('S', 0, Script),
    smt_declare_const(a, 'S', Script),
    smt_declare_const(x, 'Int', Script),
    smt_declare_datatype('DT', [[cons, [hd, 'S'], [tl, 'DT']], [nil]], Script),
    smt_declare_datatypes([[list, 0]], [[[cons, [head, 'Int'], [tail, list]], [nil]]], Script),
    smt_define_funs_rec([[factorial, [[n, 'Int']], 'Int'],[fibonacci, [[n, 'Int']], 'Int']],[[ite, [<=, n, 1], 1, [*, n, [factorial, [-, n, 1]]]],[ite, [<=, n, 1], n, [+, [fibonacci, [-, n, 1]], [fibonacci, [-, n, 2]]]]], Script),
    smt_set_logic('QF_LIA', Script),
    smt_define_sort('MyInt', [], 'Int', Script),
    smt_define_fun(f, [[x, 'Int'], [y, 'Int']], 'Int', ['+', x, y], Script),
    smt_assert([<, [f, x, 2], 5], Script),
    smt_check_sat(Script),
    smt_get_model(Script),
    smt_get_assertions(Script),
    smt_get_proof(Script),
    smt_get_unsat_core(Script),
    smt_get_assignment(Script),
    smt_get_unsat_assumptions(Script),
    smt_get_value([[f, 1, 2],a], Script),
    smt_get_option(print-success, Script),
    smt_get_info(status, Script),
    smt_push(1, Script),
    smt_pop(1, Script),
    smt_echo('Hello, world!', Script),
    smt_reset_assertions(Script),
    smt_exit(Script),

    smt_solve_with_z3(Script),
    smt_close_stream(Script).






% Tests constraint transformation functionality
models_to_constraint:-
    smt_new_stream('multiplesModelToConstraint',Script),
    smt_cvc4_options(Script),
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    smt_declare_fun('z', [], 'Int', Script),
    smt_assert([>, x, y], Script),
    smt_assert([>, y, z], Script),
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y,z], Script), % x, y and z will be transformed into a constraint
    smt_solve_with_cvc4(Script),
    % First Solve : The constrait will be (x≠x_from_model OR y≠y_from_model OR z≠z_from_model)
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script), % x and y will be transformed into a constraint
    smt_get_model_to_constraint_for([z], Script), % z will be transformed into a constraint
    smt_solve_with_cvc4(Script),
    % Second Solve : Because [x,y] and [z] are separate, the constraints will be separate. We'll have (x≠x_from_model OR y≠y_from_model) AND (z≠z_from_model)
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script), % x and y will be transformed into a constraint
    smt_get_model_to_constraint_for([x,z], Script), % x and z will be transformed into a constraint
    smt_solve_with_cvc4(Script),
    % Third Solve : This time we'll have (x≠x_from_model OR y≠y_from_model) AND (x≠x_from_model OR z≠z_from_model)
    smt_close_stream(Script).






% Shows the usefulness of Prolog's recursive calls and sat checking for exploring the solution set
get_all_sums(N) :-
    smt_new_stream('getSums', Script),
    smt_cvc4_options(Script),
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    % X and Y Greater than 0
    smt_assert([>=, x, 0], Script),
    smt_assert([>=, y, 0], Script),
    % Y + X = N
    smt_assert([=, N, [+, x, y]], Script),
    get_sums(Script),
    smt_close_stream(Script).
    
    get_sums(Script) :-
        smt_check_sat_continue_if_sat(Script), % Declares that we will check if check_sat=sat at solve time
        smt_get_model_to_constraint_for([x,y], Script), % x and y will be transformed into a constraint to explore different solutions
        (smt_solve_with_yices(Script) -> get_sums(Script) ; true). % If check_sat=sat, we look for a new solution. Otherwise we stop.






% Shows hot to get value from a model to Prolog
get_value:-
    smt_new_stream('getValue', Script),
    smt_declare_const(x, 'Int', Script),
    smt_declare_const(y, 'Int', Script),
    smt_assert([=,y,10], Script),
    smt_assert([=,y,[*,2,x]], Script),
    smt_check_sat(Script),
    smt_get_model(Script),
    smt_solve_with_z3(Script),
    smt_get_last_model_value(x,X,Script),
    write('\nValue of X:'),
    write(X),
    smt_close_stream(Script).






% Task Optimization by minimization
minimize:-
    % Creation of a stream and a "task_example.smt2" file to hold the script
    smt_new_stream(task_exemple, Stream),

    % Declaration of variables (representing the start of each task)
    smt_declare_const( startT1, 'Int', Stream),
    smt_declare_const( startT2, 'Int', Stream),
    smt_declare_const( startT3, 'Int', Stream),
    smt_declare_const( startT4, 'Int', Stream),

    % Declaration of job duration
    smt_define_fun(durationT1, [], 'Int', [3], Stream),
    smt_define_fun(durationT2, [], 'Int', [2], Stream),
    smt_define_fun(durationT3, [], 'Int', [4], Stream),
    smt_define_fun(durationT3, [], 'Int', [6], Stream),

    % Constraint: T1 must start at time 0
    smt_assert([=, startT1, 0], Stream),

    % Constraint: T2 cannot start before the end of T1
    smt_assert([>=, startT2, [+, startT1, durationT1]], Stream),

    % Constraint: T3 and T4 cannot begin before the end of T2
    smt_assert([>=, startT3, [+, startT2, durationT2]], Stream),
    smt_assert([>=, startT4, [+, startT2, durationT2]], Stream),

    % Objective: minimize total completion time
    smt_define_fun(endT3, [], 'Int', [+, startT3, durationT3], Stream),
    smt_define_fun(endT4, [], 'Int', [+, startT4, durationT4], Stream),
    smt_declare_const(endMax, 'Int', Stream),

    smt_assert([>=, endMax, endT3], Stream),
    smt_assert([>=, endMax, endT4], Stream),
    smt_assert([or, [=, endMax, endT3], [=, endMax, endT4]], Stream),

    smt_parse('(minimize endMax)', Stream), % Use of smt_parse to have access to z3

    smt_check_sat(Stream),
    smt_get_value([endMax], Stream),

    smt_solve_with_z3(Stream),

    smt_close_stream(Stream).






% N-Queens: Gets all N-Queens solutions for N, checks and prints them
queens_all_solutions(N):-
    smt_new_stream('NqueensAllSolution', Script),
    queens_declaration(N, Script),
    queens_on_board(0, N, Script),
    queens_not_same_row(N, Script),
    smt_define_fun('diagonal-threat', [['x1','Int'], ['y1','Int'], ['x2','Int'], ['y2','Int']], 'Bool', [=, [abs, [-, 'x1', 'x2']], [abs, [-, 'y1', 'y2']]], Script),
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
        findall(Queen, (between(0, PrecN, I), atom_concat('r', I, Queen)), 
                Queens),
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

    % List all N rows    
    allrows(N, Rows) :-
        succ(PrecN,N),
        numlist(0, PrecN, NumList),
        maplist(row_var, NumList, Rows).
        
    row_var(N, RowVar) :-
        atom_concat('r', N, RowVar).

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

    % Retrieve the solution in an array
    queens_get_solution(_, N, N, []).
    queens_get_solution(Script, N, I, [Value | Rest]) :-
        I < N,
        atom_concat('r', I, Var),
        smt_get_last_model_value(Var, Value, Script),
        I1 is I + 1,
        queens_get_solution(Script, N, I1, Rest).

    % Check if the solution is valid
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

    % Write all solutions
    writeAllSolutions([]).
    writeAllSolutions([Solution | Rest]) :-
        writeln(Solution),
        print_board(Solution),
        writeAllSolutions(Rest).

    % Print the board
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