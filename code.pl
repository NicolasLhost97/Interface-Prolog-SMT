:- consult(interfaceStream).

checkParsing() :-
    smt_new('checkParsing',Script),
    smt_declare_fun('x', [], 'Int', X),
    smt_declare_fun('y', [], 'Int', Y),
    smt_declare_fun('f', ['Int','Int'], 'Int',F),
    smt_parse('(assert (= (f x y) 10))', Parsed),
    smt_check_sat(Sat),
    smt_get_model(Mod),
    smt_exit(Ex),
    Script = [X,Y,F,Parsed,Sat,Mod,Ex],
    smt_solve_cvc4(Script),
    smt_close(Script).
    

checkAllParsing() :-
    smt_new('checkAllParsing',Script),
    % Générer les commandes SMT-LIB
    smt_set_info(status, unknown, Script),
    smt_set_option(interactive-mode, true, Script),
    smt_set_option(produce-proofs, true, Script),
    smt_set_option(produce-unsat-cores, true, Script),
    smt_set_option(produce-unsat-assumptions, true, Script),
    smt_set_option(print-success, true, Script),
    smt_declare_sort('S', 0, Script),
    smt_declare_const('a', 'S', Script),
    smt_declare_const('x', 'Int', Script),
    smt_declare_datatype('DT', [[cons, [hd, 'S'], [tl, 'DT']], [nil]], Script),
    write('test'),
    smt_declare_datatypes([[list, 0]], [[[cons, [head, 'Int'], [tail, list]], [nil]]], Script),
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
    smt_get_value([[symbol(f), symbol(1), symbol(2)],symbol(a)], Script),
    smt_get_option(print-success, Script),
    smt_get_info(status, Script),
    smt_push(1, Script),
    smt_pop(1, Script),
    smt_echo("Hello, world!", Script),
    smt_reset_assertions(Script),
    smt_exit(Script),
    smt_solve_z3(Script),
    smt_close(Script).


sudoku() :-
    %charger Fichier Sudoku
    smt_load_file('smt/test.smt2',[], SudokuScript),
    write(SudokuScript),
    smt_solve_cvc4(SudokuScript).
    %Récuperer les infos dans le sat, rajouter les contraintes et rechecker sat


multiplesModelToConstraintCVC4():-
    smt_new('multiplesModelToConstraint',Script),
    smt_cvc4_options(Script),
    %First Solve
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    smt_declare_fun('z', [], 'Int', Script),
    smt_assert([>, x, y], Script),
    smt_assert([>, y, z], Script),
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script),
    smt_get_model_to_constraint_for([z], Script),
    smt_solve_cvc4(Script),
    % Second Solve
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y,z], Script),
    smt_solve_cvc4(Script),
    % Third Solve
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script),
    smt_get_model_to_constraint_for([x,z], Script),
    smt_solve_cvc4(Script),
    smt_close(Script).

multiplesModelToConstraintZ3():-
    smt_new('multiplesModelToConstraint',Script),
    %First Solve
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    smt_declare_fun('z', [], 'Int', Script),
    smt_assert([>, x, y], Script),
    smt_assert([>, y, z], Script),
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script),
    smt_get_model_to_constraint_for([z], Script),
    smt_solve_z3(Script),
    % Second Solve
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y,z], Script),
    smt_solve_z3(Script),
    % Third Solve
    smt_check_sat(Script),
    smt_get_model_to_constraint_for([x,y], Script),
    smt_get_model_to_constraint_for([x,z], Script),
    smt_solve_z3(Script),
    smt_close(Script).

testSat() :-
    smt_new('testSat', Script),
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    % X and Y Greater than O
    smt_assert([>, x, 0], Script),
    smt_assert([>, y, 0], Script),
    % Y Less than O
    smt_assert([<, y, 10], Script),
    % Y Greather than X
    smt_assert([>, y, x], Script),
    add_assert_greater_than(Script, 1, 20).

add_assert_greater_than(_, Counter, Limit) :- Counter > Limit, !.
add_assert_greater_than(Script, Counter, Limit) :-
    smt_assert([>, x, Counter], Script),
    smt_check_sat_continue_if_sat(Script),
    smt_get_model(Script),
    NewCounter is Counter + 1,
    (smt_solve_z3(Script) -> add_assert_greater_than(Script, NewCounter, Limit) ; true).
    