:- use_module(library(smtlib)).
:- use_module(library(readutil)).

:- dynamic solve_counter/1.
solve_counter(0).

:- dynamic model_counter/1.
model_counter(0).


% Lancer swiprolog dans le terminal: swipl
% Se déplacer dans le dossier: working_directory(CWD,'/Users/nicolaslhost/Prolog').
% Ouvir fichier pour avoir accès aux prédicats: [fichier].



% USE OF SOLVER
% smt_solve_z3 and smt_solve_cvc4 to use a specific solver to resolve the script
% They retrieve the new script with new constraints from the model if asked

    % Create new Stream
    smt_new(FileName, Stream) :-
        %concat FileName and extension .smt2
        atom_concat(FileName, '.smt2', File),
        open(File, write, Stream).

    smt_close(Stream) :-
        close(Stream).

    % Options to add at the begining to avoid warning from CVC4
    smt_cvc4_options(Stream) :-
        smt_set_logic('ALL', Stream),
        smt_set_option('produce-models', 'true', Stream).

    % Utilisation du solver Z3 pour la résolution du Script
    smt_solve_z3(Stream) :-
        smt_solve(Stream, 'z3 ', '').

    % Utilisation du solver Z3 pour la résolution du Script
    smt_solve_cvc4(Stream) :-
        smt_solve(Stream, 'cvc4 ', ' --incremental --fmf-bound ').
        
    % Résolution du Script et avec le Solver choisi
    smt_solve(Stream, Solver, Options) :-
        stream_property(Stream, file_name(FileName)),
        flush_output(Stream),
        % Create the command to solve and save the output into a file
        sub_atom(FileName, 0, _, 5, Name),
        atom_concat(Name, '.result.smt2', ResultFile),
        atom_concat(' > ', ResultFile, ToResultFile),
        atom_concat(FileName, ToResultFile, Command),
        atom_concat(Solver, Options, SolverOptions),
        atom_concat(SolverOptions, Command, ShellCommand),
        % Use of shell (not really ISO-Prolog)
        shell(ShellCommand),
        % Get the ouput
        read_file(ResultFile, Output),
        % Show result in terminal
        write(Output),
        smtlib_read_expressions(ResultFile, Expressions),
        write('\n\n-----------------------\n\n'),
        write(Expressions),
        extract_funs_from_model_to_constraints(Expressions, ModelConstraints),
        % write('\n\n Constraints'),
        % write(ModelConstraints),
        smtlib_write_to_stream(Stream, list(ModelConstraints)),
        % Set the solve_counter to be equal to the model_counter
        model_counter(ModelCounter),
        retractall(solve_counter(_)),
        asserta(solve_counter(ModelCounter)).
        % check_continue_conditions(Expressions).




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
        open(File, read, ReadStream),
        read_file_stream(ReadStream, Codes),
        close(ReadStream),
        atom_codes(Content, Codes).


    % Read a stream to a list of character codes
    read_file_stream(Stream, Content) :-
        get_code(Stream, Code),
        read_file_stream(Code, Stream, Content).

    read_file_stream(-1, _, []) :- !. % End of file
    read_file_stream(Code, Stream, [Code|Content]) :-
        get_code(Stream, NextCode),
        read_file_stream(NextCode, Stream, Content).


% SCRIPTS PREDICATES

    % Prédicat pour utiliser directement du SMT-LIB2
    smt_parse(Expr, Stream) :-
        write(Stream, Expr),
        write(Stream,'\n').

    % Prédicat pour générer une commande "assert"
    smt_assert(Expr, Stream) :-
        convert_to_symbols(Expr, ExprSymbols),
        Command = [reserved('assert'), ExprSymbols],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "check-sat"
    smt_check_sat(Stream) :-
        Command = [reserved('check-sat')],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "check-sat" et vérifier si sat
    smt_check_sat_continue_if_sat(Stream) :-
        writeln(Stream, '(echo "continue-if-sat")'),
        smt_check_sat(Stream).
    
    % Prédicat pour générer une commande "check-sat" et vérifier si unsat
    smt_check_sat_continue_if_unsat(Stream) :-
        writeln(Stream, '(echo "continue-if-unsat")'),
        smt_check_sat(Stream).
    

    % Prédicat pour générer une commande "check-sat-assuming"
    smt_check_sat_assuming(PropLiterals, Stream) :-
        Command = [reserved('check-sat-assuming'), PropLiterals],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "declare-const"
    % Example: smt_declare_fun('w', 'Int', Stream)
    smt_declare_const(Name, Sort, Stream) :-
        Command = [reserved('declare-const'), symbol(Name), symbol(Sort)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "declare-datatype"
    smt_declare_datatype(Name, DatatypeDec, Stream) :-
        Command = [reserved('declare-datatype'), symbol(Name), DatatypeDec],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "declare-datatypes"
    smt_declare_datatypes(SortDeclarations, DatatypeDeclarations, Stream) :-
        Command = [reserved('declare-datatypes'), SortDeclarations, DatatypeDeclarations],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "declare-fun"
    % Example: smt_declare_fun('f', ['Int','Int'], 'Int', Stream)
    smt_declare_fun(Name, Args, ReturnType, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        Command = [reserved('declare-fun'), symbol(Name), ArgsSymbols, symbol(ReturnType)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "declare-sort"
    smt_declare_sort(Name, Arity, Stream) :-
        Command = [reserved('declare-sort'), symbol(Name), numeral(Arity)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "define-fun"
    smt_define_fun(Name, Args, ReturnType, Body, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        convert_to_symbols(Body, BodySymbols),
        Command = [reserved('define-fun'), symbol(Name), ArgsSymbols, symbol(ReturnType), BodySymbols],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "define-fun-rec"
    smt_define_fun_rec(Name, Args, ReturnType, Body, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        convert_to_symbols(Body, BodySymbols),
        Command = [reserved('define-fun-rec'), symbol(Name), ArgsSymbols, symbol(ReturnType), BodySymbols],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "define-funs-rec"
    smt_define_funs_rec(FunctionDecs, Bodies, Stream) :-
        Command = [reserved('define-funs-rec'), FunctionDecs, Bodies],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "define-sort"
    smt_define_sort(Name, Args, Sort, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        Command = [reserved('define-sort'), symbol(Name), ArgsSymbols, symbol(Sort)],
        smtlib_write_to_stream(Stream, Command). 
    
    % Prédicat pour générer une commande "echo"
    smt_echo(String, Stream) :-
        Command = [reserved(echo), string(String)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "exit"
    smt_exit(Stream) :-
        Command = [reserved(exit)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-assertions"
    smt_get_assertions(Stream) :-
        Command = [reserved('get-assertions')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-assignment"
    smt_get_assignment(Stream) :-
        Command = [reserved('get-assignment')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-info"
    smt_get_info(Info, Stream) :-
        Command = [reserved('get-info'), keyword(Info)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-model"
    smt_get_model(Stream) :-
        Command = [reserved('get-model')],
        smtlib_write_to_stream(Stream, Command).
    
    smt_get_model_to_constraint_for(Symbols, Stream) :-
        % Increment the model_counter
        retract(model_counter(Counter)),
        NewCounter is Counter + 1,
        asserta(model_counter(NewCounter)),
    
        atom_concat('(echo "model-to-constraint-start-', NewCounter, TempStartTag),
        atom_concat(TempStartTag, '") ; used to indentify the model coverted to constraints', FinalStartTag),
        smt_parse(FinalStartTag, Stream),

        list_symbols_to_string(Symbols, SymbolsString),
        string_concat('(echo "', SymbolsString, Begining),
        string_concat(Begining, '") ; symbols coverted to constraints', SymbolsCommand),
        smt_parse(SymbolsCommand, Stream),

        smtlib_write_to_stream(Stream, [reserved('get-model')]),

        atom_concat('(echo "model-to-constraint-end-', NewCounter, TempEndTag),
        atom_concat(TempEndTag, '") ; used to indentify the model coverted to constraints', FinalEndTag),
        smt_parse(FinalEndTag, Stream).

    % Prédicat pour générer une commande "get-option"
    smt_get_option(Option, Stream) :-
        Command = [reserved('get-option'), keyword(Option)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-proof"
    smt_get_proof(Stream) :-
        Command = [reserved('get-proof')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-unsat-assumptions"
    smt_get_unsat_assumptions(Stream) :-
        Command = [reserved('get-unsat-assumptions')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-unsat-core"
    smt_get_unsat_core(Stream) :-
        Command = [reserved('get-unsat-core')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "get-value"
    smt_get_value(Terms, Stream) :-
        Command = [reserved('get-value'), Terms],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "push"
    smt_push(N, Stream) :-
        Command = [reserved('push'), numeral(N)],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "pop"
    smt_pop(N, Stream) :-
        Command = [reserved('pop'), numeral(N)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "reset"
    smt_reset(Stream) :-
        Command = [reserved(reset)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "reset-assertions"
    smt_reset_assertions(Stream) :-
        Command = [reserved('reset-assertions')],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "set-info"
    smt_set_info(Keyword, Value, Stream) :-
        Command = [reserved('set-info'), [keyword(Keyword), symbol(Value)]],
        smtlib_write_to_stream(Stream, Command).

    % Prédicat pour générer une commande "set-logic"
    smt_set_logic(Logic, Stream) :-
        Command = [reserved('set-logic'), symbol(Logic)],
        smtlib_write_to_stream(Stream, Command).
    
    % Prédicat pour générer une commande "set-option"
    smt_set_option(Option, Bool, Stream) :-
        Command = [reserved('set-option'), keyword(Option), symbol(Bool)],
        smtlib_write_to_stream(Stream, Command).



    % Transformation en symbol
    smt_symbol(X, symbol(S)) :- atom(X), !, S = X.
    smt_symbol(X, X).

    convert_to_symbols([], []).
    convert_to_symbols([H|T], [symbol(H)|ConvertedT]) :-
            atomic(H), !,
            convert_to_symbols(T, ConvertedT).
    convert_to_symbols([H|T], [ConvertedH|ConvertedT]) :-
            is_list(H),
            convert_to_symbols(H, ConvertedH),
            convert_to_symbols(T, ConvertedT).



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


% SAT OR UNSAT CHECKING
    check_continue_conditions([]).
    check_continue_conditions([symbol('continue-if-sat'), symbol('sat') | Rest]) :-
        check_continue_conditions(Rest).
    check_continue_conditions([string('continue-if-sat'), symbol('sat') | Rest]) :-
        check_continue_conditions(Rest).
    check_continue_conditions([symbol('continue-if-unsat'), symbol('unsat') | Rest]) :-
        check_continue_conditions(Rest).
    check_continue_conditions([string('continue-if-unsat'), symbol('unsat') | Rest]) :-
        check_continue_conditions(Rest).
    check_continue_conditions([_ | Rest]) :-
        check_continue_conditions(Rest).




% MODEL EXTRACTION
    is_model_to_constraint_start_tag_and_modelID(symbol(Atom), ModelID) :-
        atom_concat('model-to-constraint-start-', ModelID, Atom).
    is_model_to_constraint_start_tag_and_modelID(string(Atom), ModelID) :-
        atom_concat('model-to-constraint-start-', ModelID, Atom).

    is_model_to_constraint_end_tag(symbol(Atom)) :-
        atom_concat('model-to-constraint-end-', _, Atom).
    is_model_to_constraint_end_tag(string(Atom)) :-
        atom_concat('model-to-constraint-end-', _, Atom).

    get_funs_list([symbol('model') | Funs], Funs).
    get_funs_list(Funs, Funs) :- \+ member(symbol('model'), Funs).

    extract_funs_from_model_to_constraints(Input, Result) :-
        extract_funs_from_model_to_constraints(Input, [], Result).

    extract_funs_from_model_to_constraints([], Accum, Accum).
    extract_funs_from_model_to_constraints([StartTag, ConstraintSymbolsRaw, Funs, EndTag | Rest], Accum, Result) :-
        % Find Start Tag and Model ID
        is_model_to_constraint_start_tag_and_modelID(StartTag, ModelID),
        atom_to_number(ModelID, ModelIDNumber),
        % Check the modelID to avoid retrieving constraints from an already processed model
        solve_counter(SolveCounter),
        ModelIDNumber > SolveCounter,
        % Find End Tag
        is_model_to_constraint_end_tag(EndTag),
        % Retrieve all funs in the model
        get_funs_list(Funs, FunsList),
        % Constraint Symbols form normalization (difference w/ solver)
        check_constraint_symbols_form(ConstraintSymbolsRaw, ConstraintSymbols),
        % Select Funs which are wanted
        funs_selection(ConstraintSymbols, FunsList, SelectedFuns),
        % Transform names to add _from_model
        transform_model_symbol_name(SelectedFuns, ModelID, RenamedFuns),
        % Create Constraints
        create_constraints_assert(ConstraintSymbols, ModelID, Asserts),
        % Unite Assert Constraints & Model Funs
        append(RenamedFuns, Asserts, ModelConstraints),
        append(Accum, ModelConstraints, NewAccum),
        % Continue
        extract_funs_from_model_to_constraints(Rest, NewAccum, Result).
    extract_funs_from_model_to_constraints([StartTag | Rest], Accum, Result) :-
        is_model_to_constraint_start_tag_and_modelID(StartTag, ModelID),
        atom_to_number(ModelID, ModelIDNumber),
        solve_counter(SolveCounter),
        ModelIDNumber =< SolveCounter,
        extract_funs_from_model_to_constraints(Rest, Accum, Result).
    extract_funs_from_model_to_constraints([_ | Rest], Accum, Result) :-
        extract_funs_from_model_to_constraints(Rest, Accum, Result).

    % Check if form is[symbol(x),symbol(y)] otherwise normalise it
    check_constraint_symbols_form(ConstraintSymbolsRaw, ConstraintSymbols) :-
        (is_list_of_symbols(ConstraintSymbolsRaw) ->
            ConstraintSymbols = ConstraintSymbolsRaw
        ;
            normalize_constraint_symbols(ConstraintSymbolsRaw, ConstraintSymbols)
        ).
    
    is_list_of_symbols([]).
    is_list_of_symbols([symbol(_) | Tail]) :-
        is_list_of_symbols(Tail).
    
    % Normalise Constraint symbols to the form: [symbol(x),symbol(y)]
    normalize_constraint_symbols(string(Str), Symbols) :-
        atom_concat('(', WithoutLeftParenthesis, Str),
        atom_concat(WithoutSpaces, ')', WithoutLeftParenthesis),
        atomic_list_concat(Atoms, ' ', WithoutSpaces),
        maplist(atom_to_symbol, Atoms, Symbols).
    normalize_constraint_symbols(Symbols, Symbols) :-
        is_list(Symbols),
        maplist(symbol, Symbols).
    
    atom_to_symbol(Atom, symbol(Atom)).
    
    
        
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
    create_constraints_assert(List, ModelID, Constraints) :-
        create_constraints_assert_helper(List, ModelID, Disjuncts),
        (Disjuncts = [] -> Constraints = [];
            (Disjuncts = [SingleDisjunct] -> Constraints = [[reserved(assert), SingleDisjunct]];
                Constraints = [[reserved(assert), [symbol(or) | Disjuncts]]])).

    create_constraints_assert_helper([], _, []).
    create_constraints_assert_helper([symbol(Var) | Rest], ModelID, [[symbol(not), [symbol(=), symbol(Var), symbol(VarFromModel)]] | AssertionsRest]) :-
        atom_concat(Var, '_from_model_', TempVarFromModel),
        atom_concat(TempVarFromModel, ModelID, VarFromModel),
        create_constraints_assert_helper(Rest, ModelID, AssertionsRest).

            
    % Add "_from_model" to differentiate symbols from model
    transform_model_symbol_name([], _, []).
    transform_model_symbol_name([[reserved('define-fun'), symbol(Var) | Rest] | Tail], ModelID, [[reserved(define-fun), symbol(VarFromModel)| Rest] | TransformedTail]) :-
        atom_concat(Var, '_from_model_', VarFromModelPartial),
        atom_concat(VarFromModelPartial, ModelID, VarFromModel),
        transform_model_symbol_name(Tail, ModelID, TransformedTail).


    
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

    % Convert an atom to a number
    atom_to_number(Atom, Number) :-
        atom_chars(Atom, Chars),
        number_chars(Number, Chars).

    % Convert a number to an atom
    number_to_atom(Number, Atom) :-
        number_chars(Number, Chars),
        atom_chars(Atom, Chars).

