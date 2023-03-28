:- consult(interfaceStream).

checkParsing() :-
    smt_declare_fun('x', [], 'Int', X),
    smt_declare_fun('y', [], 'Int', Y),
    smt_declare_fun('f', ['Int','Int'], 'Int',F),
    smt_parse('(assert (= (f x y) 10))', Parsed),
    smt_check_sat(Sat),
    smt_get_model(Mod),
    smt_exit(Ex),
    Script = [X,Y,F,Parsed,Sat,Mod,Ex],
    smt_solve_cvc4(Script).
    

checkAllParsing() :-
    smt_load_file('smt/parsingTest.smt2', [], Script),
    write(Script),
    write('\n\n\n'),
    % générer les commandes SMT-LIB
    smt_set_info(status, unknown, SetInfo),
    smt_set_option(interactive-mode, true, SetOption1),
    smt_set_option(produce-proofs, true, SetOption2),
    smt_set_option(produce-unsat-cores, true, SetOption3),
    smt_set_option(produce-unsat-assumptions, true, SetOption4),
    smt_set_option(print-success, true, SetOption5),
    smt_declare_sort('S', 0, DeclareSort),
    smt_declare_const('a', 'S', DeclareConst1),
    smt_declare_const('x', 'Int', DeclareConst2),
    smt_declare_datatype(DT, [[cons, [hd, 'S'], [tl, DT]], [nil]], DeclareDatatype),
    smt_declare_datatypes([[list, 0]], [[[cons, [head, 'Int'], [tail, list]], [nil]]], DeclareDatatypes),
    smt_set_logic('QF_LIA', SetLogic),
    smt_define_sort('MyInt', [], 'Int', DefineSort),
    smt_define_fun(f, [[x, 'Int'], [y, 'Int']], 'Int', ['+', x, y], DefineFun),
    smt_assert([<, [f, x, 2], 5], Assert1),
    smt_check_sat(CheckSat),
    smt_get_model(GetModel),
    smt_get_assertions(GetAssertions),
    smt_get_proof(GetProof),
    smt_get_unsat_core(GetUnsatCore),
    smt_get_assignment(GetAssignment),
    smt_get_unsat_assumptions(GetUnsatAssumptions),
    smt_get_value([[symbol(f), symbol(1), symbol(2)],symbol(a)], GetValue),
    smt_get_option(print-success, GetOption),
    smt_get_info(status, GetInfo),
    smt_push(1, Push),
    smt_pop(1, Pop),
    smt_echo("Hello, world!", Echo),
    smt_reset_assertions(ResetAssertions),
    smt_exit(Exit),

    % rassembler toutes les commandes dans une liste
    Script2 = [SetInfo, SetOption1, SetOption2, SetOption3, SetOption4, SetOption5, 
            DeclareSort, DeclareConst1, DeclareConst2, DeclareDatatype, DeclareDatatypes, 
            SetLogic, DefineSort, DefineFun, Assert1, 
            CheckSat, GetModel, GetAssertions, GetProof, GetUnsatCore, 
            GetAssignment, GetUnsatAssumptions, GetValue, GetOption, GetInfo, 
            Push, Pop, Echo, ResetAssertions, Exit],

    write(Script2).

codeAndFile() :-
    % Déclaration de fonctions
    smt_declare_fun('x', [], 'Int', X),
    smt_declare_fun('y', [], 'Int', Y),
    smt_declare_fun('z', [], 'Int', Z),
    % Assertions
    smt_assert([symbol(>), symbol(x), symbol(y)], Assert1),
    smt_assert([symbol(>), symbol(y), symbol(z)], Assert2),
    % smt_assert([symbol(>), symbol(z), symbol(x)], Assert3),
    % smt_assert_2(x > y, Assert1),
    % smt_assert_2(y > z, Assert2),  
    % Check-sat
    smt_check_sat(CheckSat),
    % Get-Model and transform model to constraint for some funs
    smt_get_model_to_constraint_for([x,y], GetModel),
    % Création du script final
    Script = [X, Y, Z, Assert1, Assert2, CheckSat, GetModel],
    % Solve
    smt_solve_z3(Script, ScriptWithModelConstraint),
    ScriptEnd = [CheckSat,GetModel],
    append(ScriptWithModelConstraint, ScriptEnd, FinalScript),
    smt_solve_z3(FinalScript, _).


sudoku() :-
    %charger Fichier Sudoku
    smt_load_file('smt/test.smt2',[], SudokuScript),
    write(SudokuScript),
    smt_solve_cvc4(SudokuScript,_).
    %Récuperer les infos dans le sat, rajouter les contraintes et rechecker sat


testInterface():-
    smt_new('testInterfaceWriting2',Script),
    % Déclaration de fonctions
    smt_declare_fun('x', [], 'Int', Script),
    smt_declare_fun('y', [], 'Int', Script),
    smt_declare_fun('z', [], 'Int', Script),
    % Assertions
    smt_assert([>, x, y], Script),
    smt_assert([>, y, z], Script),
    % Check-sat
    smt_check_sat(Script),
    % Get-Model and transform model to constraint for some funs
    smt_get_model_to_constraint_for([x,y], Script),
    smt_solve_z3(Script),
    % Check-sat
    smt_check_sat(Script),
    % Get-Model and transform model to constraint for some funs
    smt_get_model_to_constraint_for([x,y], Script),
    smt_solve_z3(Script),
    smt_close(Script).
