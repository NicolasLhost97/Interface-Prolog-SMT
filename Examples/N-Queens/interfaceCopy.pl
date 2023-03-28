% :- use_module(library(clpfd)).
:- use_module(library(smtlib)).
:- use_module(library(readutil)).


% Lancer swiprolog dans le terminal: swipl
% Se déplacer dans le dossier: working_directory(CWD,'/Users/nicolaslhost/Prolog').
% Ouvir fichier pour avoir accès aux prédicats: [fichier].



% USE OF SOLVER
% smt_solve_z3 and smt_solve_cvc4 to use a specific solver to resolve the script
% They retrieve the new script with new constraints from the model if asked

    % Utilisation du solver Z3 pour la résolution du Script
    smt_solve_z3(Script, NewScript) :-
        smt_solve(Script, 'z3', SolverOutput),
        smt_solve_create_new_script(Script, SolverOutput, NewScript).

    % Utilisation du solver Z3 pour la résolution du Script
    smt_solve_cvc4(Script, NewScript) :-
        % Ajout option produce-models pour afficher le model (non natif avec CVC4)
        % Ajout d'un logique par défaut pour éviter des warning dans la réponse
        smt_set_option('produce-models', 'true', ModelOption),
        smt_set_option('incremental', 'true', IncrementalOption),
        smt_set_option('fmf-bound', 'true', BoundOption),
        smt_set_logic('ALL', AllLogic),
        smt_solve([AllLogic,ModelOption,IncrementalOption,BoundOption|Script], 'cvc4', SolverOutput),
        smt_solve_create_new_script(Script, SolverOutput, NewScript).

    % Résolution du Script et récupération de l'Output du Solver choisi
    smt_solve(Script, Solver, Output) :-
        % Ecrire le nouveau code dans un fichier et le lancer avec Z3
        smtlib_write_to_file('temp.smt2', list(Script)),
        process_create(path(Solver), ['temp.smt2'], [process(PID), stdout(pipe(Out))]),
        % attendre que Z3 se termine
        process_wait(PID, _),
        % écrire la sortie de Z3 dans le fichier de sortie
        open('result.smt2', write, Stream),
        copy_stream_data(Out, Stream),
        close(Stream),
        close(Out),
        % lire le résultat de Z3 à partir du fichier de sortie
        read_file('result.smt2', Output),
        % afficher le résultat dans la console
        write(Output).

    % Crée un NewScript à partir du Script et de l'output du solver correspondant avec
    % récupération des données du modele pour créer de nouvelles contraintes
    smt_solve_create_new_script(Script, SolverOutput, NewScript) :-
        smtlib_read_expressions('result.smt2', Expressions),
        write('\n\n\n-----------------------\n\n\n'),
        extract_funs_from_model_to_constraints(Expressions, ModelConstraints),
        write('\n\n'+ModelConstraints),
        append(Script,ModelConstraints,NewScript).
          


% UTILS FOR USAGE OF SMT FILES

    % Write the script into a file
    smt_write_file(File, Script) :-
        % ecrire dans le fichier file
        smtlib_write_to_file(File, list(Script)).

    % Load a file to add at the end of an existing script
    smt_load_file(File, Script, NewScript) :-
        % lecture du Fichier
        smtlib_read_script(File, list(SMTLines)),
        % rajouter le code Prolog
        append(Script, SMTLines, NewScript).

    % Directly solve a file
    % Use Z3 by default (can be change for 'cvc4' or other supported)
    smt_solve_file(File) :-
        smt_load_file(File, [], Script),
        smt_solve(Script, 'z3', _).

    % Read a file and transform it to Atom
    read_file(File, Content) :-
        open(File, read, Stream),
        read_stream_to_codes(Stream, Codes),
        close(Stream),
        atom_codes(Content, Codes).




% SCRIPTS PREDICATES

    % Prédicat pour parser du SMT-LIB2
    smt_parse(Expr, Command) :-
        string_chars(Expr,CharsExpr),
        smtlib_parse_script(CharsExpr, list([Command])).

    % Prédicat pour générer une commande "assert"
    smt_assert(Expr, Command) :-
        Command = [reserved('assert'), Expr].

    % Prédicat pour générer une commande "check-sat"
    smt_check_sat(Command) :-
        Command = [reserved('check-sat')].

    % Prédicat pour générer une commande "check-sat-assuming"
    smt_check_sat_assuming(PropLiterals, Command) :-
        Command = [reserved('check-sat-assuming'), PropLiterals].

    % Prédicat pour générer une commande "declare-const"
    % Example: smt_declare_fun('w', 'Int', W)
    smt_declare_const(Name, Sort, Command) :-
        Command = [reserved('declare-const'), symbol(Name), symbol(Sort)].
    
    % Prédicat pour générer une commande "declare-datatype"
    smt_declare_datatype(Name, DatatypeDec, Command) :-
        Command = [reserved('declare-datatype'), symbol(Name), DatatypeDec].
    
    % Prédicat pour générer une commande "declare-datatypes"
    smt_declare_datatypes(SortDeclarations, DatatypeDeclarations, Command) :-
        Command = [reserved('declare-datatypes'), SortDeclarations, DatatypeDeclarations].
  
    % Prédicat pour générer une commande "declare-fun"
    % Example: smt_declare_fun('f', ['Int','Int'], 'Int',F)
    smt_declare_fun(Name, Args, ReturnType, Command) :-
        maplist(smt_symbol, Args, SymbolArgs),
        Command = [reserved('declare-fun'), symbol(Name), SymbolArgs, symbol(ReturnType)].
    
    % Prédicat pour générer une commande "declare-sort"
    smt_declare_sort(Name, Arity, Command) :-
        Command = [reserved('declare-sort'), symbol(Name), numeral(Arity)].
    
    % Prédicat pour générer une commande "define-fun"
    smt_define_fun(Name, Args, ReturnType, Body, Command) :-
        Command = [reserved('define-fun'), symbol(Name), Args, symbol(ReturnType), Body].

    % Prédicat pour générer une commande "define-fun-rec"
    smt_define_fun_rec(Name, Args, ReturnType, Body, Command) :-
        Command = [reserved('define-fun-rec'), symbol(Name), Args, symbol(ReturnType), Body].

    % Prédicat pour générer une commande "define-funs-rec"
    smt_define_funs_rec(FunctionDecs, Bodies, Command) :-
        Command = [reserved('define-funs-rec'), FunctionDecs, Bodies].
    
    % Prédicat pour générer une commande "define-sort"
    smt_define_sort(Name, Args, Sort, Command) :-
        Command = [reserved('define-sort'), symbol(Name), Args, symbol(Sort)].   
    
    % Prédicat pour générer une commande "echo"
    smt_echo(String, Command) :-
        Command = [reserved(echo), string(String)].
    
    % Prédicat pour générer une commande "exit"
    smt_exit(Command) :-
        Command = [reserved(exit)].
    
    % Prédicat pour générer une commande "get-assertions"
    smt_get_assertions(Command) :-
        Command = [reserved('get-assertions')].
    
    % Prédicat pour générer une commande "get-assignment"
    smt_get_assignment(Command) :-
        Command = [reserved('get-assignment')].
    
    % Prédicat pour générer une commande "get-info"
    smt_get_info(Info, Command) :-
        Command = [reserved('get-info'), keyword(Info)].
    
    % Prédicat pour générer une commande "get-model"
    smt_get_model(Command) :-
        Command = [reserved('get-model')].

    % Prédicat pour générer une commande "get-model" avec extraction et convertir en contraintes 
    smt_get_model_to_constraint_for(Symbols,list(Command)) :-
        list_symbols_to_string(Symbols,SymbolsString),
        string_concat('(echo "',SymbolsString, Begining),
        string_concat(Begining,'") ; symbols coverted to constraints', AllString),
        smt_parse('(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints', ModelStart),
        smt_parse(AllString, ConstraintSymbols),
        smt_parse('(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints', ModelEnd),
        Command = [ModelStart,ConstraintSymbols,[reserved('get-model')],ModelEnd].
    
    % Prédicat pour générer une commande "get-option"
    smt_get_option(Option, Command) :-
        Command = [reserved('get-option'), keyword(Option)].
    
    % Prédicat pour générer une commande "get-proof"
    smt_get_proof(Command) :-
        Command = [reserved('get-proof')].
    
    % Prédicat pour générer une commande "get-unsat-assumptions"
    smt_get_unsat_assumptions(Command) :-
        Command = [reserved('get-unsat-assumptions')].
    
    % Prédicat pour générer une commande "get-unsat-core"
    smt_get_unsat_core(Command) :-
        Command = [reserved('get-unsat-core')].
    
    % Prédicat pour générer une commande "get-value"
    smt_get_value(Terms, Command) :-
        Command = [reserved('get-value'), Terms].

    % Prédicat pour générer une commande "push"
    smt_push(N, Command) :-
        Command = [reserved('push'), numeral(N)].

    % Prédicat pour générer une commande "pop"
    smt_pop(N, Command) :-
        Command = [reserved('pop'), numeral(N)].
    
    % Prédicat pour générer une commande "reset"
    smt_reset(Command) :-
        Command = [reserved(reset)].
    
    % Prédicat pour générer une commande "reset-assertions"
    smt_reset_assertions(Command) :-
        Command = [reserved('reset-assertions')].
    
    % Prédicat pour générer une commande "set-info"
    smt_set_info(Keyword, Value, Command) :-
        Command = [reserved('set-info'), [keyword(Keyword), symbol(Value)]].

    % Prédicat pour générer une commande "set-logic"
    smt_set_logic(Logic, Command) :-
        Command = [reserved('set-logic'), symbol(Logic)].
    
    % Prédicat pour générer une commande "set-option"
    smt_set_option(Option, Bool, Command) :-
        Command = [reserved('set-option'), keyword(Option), symbol(Bool)].



    % Transformation en symbol
    smt_symbol(X, symbol(S)) :- atom(X), !, S = X.
    smt_symbol(X, X).



% Easier Assert
    
    % Liste des opérateurs supportés
    operator('+').
    operator('-').
    operator('*').
    operator('/').
    operator('div').
    operator('mod').

    % Opérateurs de comparaison
    operator('>').
    operator('<').
    operator('>=').
    operator('<=').

    % Opérateurs logiques
    operator('and').
    operator('or').
    operator('not').
    operator('=>').
    operator('=').

   % Prédicat pour convertir les expressions Prolog en une structure intermédiaire
    expr_to_struct(X, symbol(X)) :- atom(X).
    expr_to_struct(X, numeral(X)) :- number(X).
    expr_to_struct((A, Op, B), struct(Op, SA, SB)) :-
        operator(Op),
        expr_to_struct(A, SA),
        expr_to_struct(B, SB).

    % Prédicat pour convertir une structure intermédiaire en S-expression SMT-LIB2
    struct_to_sexp(symbol(X), [symbol(X)]).
    struct_to_sexp(numeral(X), [numeral(X)]).
    struct_to_sexp(struct(Op, A, B), [symbol(Op), SA, SB]) :-
        struct_to_sexp(A, SA),
        struct_to_sexp(B, SB).

    % Prédicat pour ajouter une assertion SMT-LIB2 à partir d'une expression courrante
    smt_assert_2(Expr, Command) :-
        expr_to_struct(Expr, Struct),
        struct_to_sexp(Struct, SExpr),
        smt_assert(SExpr, Command).





% MODEL EXTRACTION
    extract_funs_from_model_to_constraints(Input, Result) :-
        extract_funs_from_model_to_constraints(Input, [], Result).

    extract_funs_from_model_to_constraints([], Accum, Accum).
    % Trouver la zone d'extraction sans ou avec le (symbol(model))
    extract_funs_from_model_to_constraints([symbol('model-to-constraint-start'), ConstraintSymbols, Funs, symbol('model-to-constraint-end') | Rest], Accum, Result) :-
        funs_selection(ConstraintSymbols, Funs, SelectedFuns),
        transform_model_symbol_name(SelectedFuns, RenamedFuns),
        create_constraints_assert(ConstraintSymbols, Asserts),
        %Unite Assert Constraints & Model Funs
        append(RenamedFuns,Asserts,ModelConstraints),
        append(Accum, ModelConstraints, NewAccum),
        extract_funs_from_model_to_constraints(Rest, NewAccum, Result).
    extract_funs_from_model_to_constraints([string('model-to-constraint-start'), ConstraintSymbols, [symbol('model') | Funs], string('model-to-constraint-end') | Rest], Accum, Result) :-
        funs_selection(ConstraintSymbols, Funs, SelectedFuns),
        transform_model_symbol_name(SelectedFuns, RenamedFuns),
        create_constraints_assert(ConstraintSymbols, Asserts),
        %Unite Assert Constraints & Model Funs
        append(RenamedFuns,Asserts,ModelConstraints),
        append(Accum, ModelConstraints, NewAccum),
        extract_funs_from_model_to_constraints(Rest, NewAccum, Result).
    % Continuer la recherche en dehors de la zone d'extraction
    extract_funs_from_model_to_constraints([_ | Rest], Accum, Result) :-
        extract_funs_from_model_to_constraints(Rest, Accum, Result).

    % Selection des Funs voulues pour devenir des contraintes.
    funs_selection(_, [], []).
    funs_selection(ConstraintSymbols, [Fun | FunsRest], [Fun | SelectedRest]) :-
        Fun = [_, Symbol | _],
        member(Symbol, ConstraintSymbols),
        funs_selection(ConstraintSymbols, FunsRest, SelectedRest).
    funs_selection(ConstraintSymbols, [Fun | FunsRest], SelectedRest) :-
        Fun = [_, Symbol | _],
        \+ member(Symbol, ConstraintSymbols),
        funs_selection(ConstraintSymbols, FunsRest, SelectedRest).

    % Create Constraints from model
    create_constraints_assert([], []).
    create_constraints_assert([symbol(Var) | Rest], [[reserved(assert), [symbol(not), [symbol(=), symbol(Var), symbol(VarFromModel)]]] | AssertionsRest]) :-
        atom_concat(Var, '_from_model', VarFromModel),
        create_constraints_assert(Rest, AssertionsRest).

    % Add "_from_model" to differentiate symbols from model
    transform_model_symbol_name([], []).
    transform_model_symbol_name([[reserved('define-fun'), symbol(Var) | Rest] | Tail], [[reserved(define-fun), symbol(VarFromModel)| Rest] | TransformedTail]) :-
        atom_concat(Var, '_from_model', VarFromModel),
        transform_model_symbol_name(Tail, TransformedTail).


    
% UTILS
    % Transform array [x,y,z] to string "(x y z)"
    list_symbols_to_string(List, Result) :-
        symbols_to_string(List, InnerResult),
        string_concat('(', InnerResult, TempResult),
        string_concat(TempResult, ')', Result).

    symbols_to_string([], '').
    symbols_to_string([Symbol], String) :-
        term_string(Symbol, String).
    symbols_to_string([Symbol|Rest], Result) :-
        term_string(Symbol, SymbolString),
        symbols_to_string(Rest, RestString),
        string_concat(SymbolString, ' ', TempResult),
        string_concat(TempResult, RestString, Result).

     % Transform string "[x,y]" to array [x,y]
     string_to_list_symbols(String, List) :-
        string_concat('(', Rest, String),
        string_concat(SymbolsString, ')', Rest),
        read_term(SymbolsString, List, [syntax_errors(quiet)]).

