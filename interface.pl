
:- consult(smtlib_iso). % Load the smtlib module with ISO modifications 

%:- use_module(library(iso_incomplete)). %If using with CIAO Prolog

:- dynamic(solve_counter/1).
solve_counter(0).
:- dynamic(model_counter/1).
model_counter(0).


% INTERACTIONS WITH SMT SOLVERS
% smt_solve_with_z3, smt_solve_with_cvc4 and smt_solve_with_yices to use a specific solver to resolve the script
% They retrieve the new script with new constraints from the model if asked

    % Create new Stream
    smt_new_stream(FileName, Stream) :-
        %concat FileName and extension .smt2
        atom_concat(FileName, '.smt2', File),
        open(File, write, Stream).
    
    % Close the stream
    smt_close_stream(Stream) :-
        close(Stream),
        retract(solve_counter(_)),
        asserta(solve_counter(0)),
        retract(model_counter(_)),
        asserta(model_counter(0)).

    % Options to add at the begining to avoid warning from CVC4
    smt_cvc4_options(Stream) :-
        smt_set_option('produce-models', 'true', Stream),
        smt_set_logic('ALL', Stream).


    % Using the Z3 solver to solve the Script
    smt_solve_with_z3(Stream) :-
        smt_solve(Stream, 'powershell z3 ', '').

    % Using the CVC4 solver to solve the Script
    smt_solve_with_cvc4(Stream) :-
        smt_solve(Stream, 'powershell cvc4 ', ' --incremental --fmf-bound ').

    % Using the Yices solver to solve the Script
    smt_solve_with_yices(Stream) :-
        smt_solve(Stream, 'powershell yices-smt2 ', '--incremental --smt2-model-format').


    % Solving the Script with a chosen Solver
    % You can use the solver of your choice, but it's better to use 
    % predicates with validated solvers like smt_solve_with_z3. 
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
        write('\n───────── Solver\'s Output ─────────\n\n'),
        write(Output),
        smtlib_read_expressions(ResultFile, Expressions),
        write('\n───────────────────────────────────\n\n'),
        % Extract values wanted from the model and transform then into constraints
        extract_funs_from_model_to_constraints(Expressions, ModelConstraints),
        smtlib_write_to_stream(Stream, list(ModelConstraints)),
        % Set the solve_counter to be equal to the model_counter
        model_counter(ModelCounter),
        retractall(solve_counter(_)),
        asserta(solve_counter(ModelCounter)),
        % Check if sat/unsat conditions are respected
        check_continue_conditions(Expressions).

    % Retrieves a chosen value from the last generated model
    smt_get_last_model_value(FunName, Value, Stream) :-
        stream_property(Stream, file_name(FileName)),
        sub_atom(FileName, 0, _, 5, Name),
        atom_concat(Name, '.result.smt2', ResultFile),
        smtlib_read_expressions(ResultFile, Expressions),
        extract_last_model(Expressions, LastModel),
        find_value_in_model(FunName, LastModel, Value).



% INTERACTIONS WITH SMT FILES
    % Write the Command to the Stream
    % Use the flush_output to write when a command is created (easier to debug) but less time efficient
    smt_write_to_stream(Stream, Command):-
        smtlib_write_to_stream(Stream, Command).
        %flush_output(Stream).

    % Load a file to add at the end of the Stream
    smt_load_file(File, Stream) :-
        % Transform the file to Commands
        smtlib_read_script(File, list(Command)),
        % Write the Commands in the Stream
        smt_write_to_stream(Stream, list(Command)).

    % Directly solve a file
    % Use Z3 by default (can be change for other supported)
    smt_solve_file(File) :-
        smtlib_read_script(File, list(Command)),
        sub_atom(File, 0, _, 5, FileName),
        smt_new_stream(FileName, Stream),
        smt_write_to_stream(Stream, list(Command)),
        smt_solve_with_z3(Stream),
        smt_close_stream(Stream).

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

    % Predicate for direct use of SMT-LIB2 command
    smt_parse(Expr, Stream) :-
        write(Stream, Expr),
        write(Stream,'\n').

    % Predicate to generate an "assert" command
    smt_assert(Expr, Stream) :-
        convert_to_symbols(Expr, ExprSymbols),
        Command = [reserved('assert'), ExprSymbols],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate an "check-sat" command
    smt_check_sat(Stream) :-
        Command = [reserved('check-sat')],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "check-sat" command and return true if sat, false otherwise
    smt_check_sat_continue_if_sat(Stream) :-
        write(Stream, '(echo "continue-if-sat")'),
        nl(Stream),
        smt_check_sat(Stream).
    
    % Predicate to generate a "check-sat" command and return true if unsat, false otherwise
    smt_check_sat_continue_if_unsat(Stream) :-
        write(Stream, '(echo "continue-if-unsat")'),
        nl(Stream),
        smt_check_sat(Stream).
    
    % Predicate for generating a "check-sat-assuming" command
    smt_check_sat_assuming(PropLiterals, Stream) :-
        Command = [reserved('check-sat-assuming'), PropLiterals],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "declare-const" command
    % Example: smt_const(w, 'Int', Stream)
    smt_declare_const(Name, Sort, Stream) :-
        Command = [reserved('declare-const'), symbol(Name), symbol(Sort)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate for generating a "declare-datatype" command
    smt_declare_datatype(Name, DatatypeDec, Stream) :-
        convert_to_symbols(DatatypeDec, DatatypeDecSymbols),
        Command = [reserved('declare-datatype'), symbol(Name), DatatypeDecSymbols],
        smt_write_to_stream(Stream, Command).
    
    % Predicate for generating a "declare-datatypes" command
    smt_declare_datatypes(SortDeclarations, DatatypeDeclarations, Stream) :-
        convert_to_symbols(SortDeclarations, SortDeclarationsymbols),
        convert_to_symbols(DatatypeDeclarations, DatatypeDeclarationsSymbols),
        Command = [reserved('declare-datatypes'), SortDeclarationsymbols, DatatypeDeclarationsSymbols],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "declare-fun" command
    % Example: smt_declare_fun('f', ['Int','Int'], 'Int', Stream)
    smt_declare_fun(Name, Args, ReturnType, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        Command = [reserved('declare-fun'), symbol(Name), ArgsSymbols, symbol(ReturnType)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "declare-sort" command
    smt_declare_sort(Name, Arity, Stream) :-
        Command = [reserved('declare-sort'), symbol(Name), numeral(Arity)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "define-fun" command
    smt_define_fun(Name, Args, ReturnType, Body, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        convert_to_symbols(Body, BodySymbols),
        Command = [reserved('define-fun'), symbol(Name), ArgsSymbols, symbol(ReturnType), BodySymbols],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "define-fun-rec" command
    smt_define_fun_rec(Name, Args, ReturnType, Body, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        convert_to_symbols(Body, BodySymbols),
        Command = [reserved('define-fun-rec'), symbol(Name), ArgsSymbols, symbol(ReturnType), BodySymbols],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "define-funs-rec" command
    smt_define_funs_rec(FunctionDecs, Bodies, Stream) :-
        convert_to_symbols(FunctionDecs, FunctionDecsSymbols),
        convert_to_symbols(Bodies, BodiesSymbols),
        Command = [reserved('define-funs-rec'), FunctionDecsSymbols, BodiesSymbols],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "define-sort" command
    smt_define_sort(Name, Args, Sort, Stream) :-
        convert_to_symbols(Args, ArgsSymbols),
        Command = [reserved('define-sort'), symbol(Name), ArgsSymbols, symbol(Sort)],
        smt_write_to_stream(Stream, Command). 
    
    % Predicate to generate an "echo" command
    smt_echo(String, Stream) :-
        Command = [reserved(echo), string(String)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate for generating an "exit" command
    smt_exit(Stream) :-
        Command = [reserved(exit)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-assertions" command
    smt_get_assertions(Stream) :-
        Command = [reserved('get-assertions')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-assignment" command
    smt_get_assignment(Stream) :-
        Command = [reserved('get-assignment')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate for generating a "get-info" command
    smt_get_info(Info, Stream) :-
        Command = [reserved('get-info'), keyword(Info)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-model" command
    smt_get_model(Stream) :-
        Command = [reserved('get-model')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-model" command in which the values of selected variables 
    % will be retrieved and automatically added to the script as a constraint. This feature 
    % is activated the next time the solver is called. It is possible to use this feature several 
    % times before calling the solver. The constraints will be written after the model found by 
    % the solver, and a new call will be required to take the constraints into account.
    smt_get_model_to_constraint_for(Symbols, Stream) :-
        % Increment the model_counter
        retract(model_counter(Counter)),
        NewCounter is Counter + 1,
        asserta(model_counter(NewCounter)),
        number_chars(NewCounter, NewCounterChars),        
        atom_chars(NewCounterAtom, NewCounterChars),

        atom_concat('(echo "model-to-constraint-start-', NewCounterAtom, TempStartTag),
        atom_concat(TempStartTag, '") ; used to indentify the model converted to constraints', FinalStartTag),
        smt_parse(FinalStartTag, Stream),

        list_symbols_to_string(Symbols, SymbolsString),
        atom_concat('(echo "', SymbolsString, Begining),
        atom_concat(Begining, '") ; symbols converted to constraints', SymbolsCommand),
        smt_parse(SymbolsCommand, Stream),

        smtlib_write_to_stream(Stream, [reserved('get-model')]),

        atom_concat('(echo "model-to-constraint-end-', NewCounterAtom, TempEndTag),
        atom_concat(TempEndTag, '") ; used to indentify the model converted to constraints', FinalEndTag),
        smt_parse(FinalEndTag, Stream).

    % Predicate to generate a "get-option" command
    smt_get_option(Option, Stream) :-
        Command = [reserved('get-option'), keyword(Option)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-proof" command
    smt_get_proof(Stream) :-
        Command = [reserved('get-proof')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-unsat-assumptions" command
    smt_get_unsat_assumptions(Stream) :-
        Command = [reserved('get-unsat-assumptions')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-unsat-core" command
    smt_get_unsat_core(Stream) :-
        Command = [reserved('get-unsat-core')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "get-value" command
    smt_get_value(Terms, Stream) :-
        convert_to_symbols(Terms, TermsSymbols),
        Command = [reserved('get-value'), TermsSymbols],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a push command
    smt_push(N, Stream) :-
        Command = [reserved('push'), numeral(N)],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "pop" command
    smt_pop(N, Stream) :-
        Command = [reserved('pop'), numeral(N)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "reset" command
    smt_reset(Stream) :-
        Command = [reserved(reset)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "reset-assertions" command
    smt_reset_assertions(Stream) :-
        Command = [reserved('reset-assertions')],
        smt_write_to_stream(Stream, Command).
    
    % Predicate for generating a "set-info" command
    smt_set_info(Keyword, Value, Stream) :-
        Command = [reserved('set-info'), keyword(Keyword), symbol(Value)],
        smt_write_to_stream(Stream, Command).

    % Predicate to generate a "set-logic" command
    smt_set_logic(Logic, Stream) :-
        Command = [reserved('set-logic'), symbol(Logic)],
        smt_write_to_stream(Stream, Command).
    
    % Predicate to generate a "set-option" command
    smt_set_option(Option, Bool, Stream) :-
        Command = [reserved('set-option'), keyword(Option), symbol(Bool)],
        smt_write_to_stream(Stream, Command).
    
    extract_value_from_variable_value([(_, Value)], Value).



% SAT OR UNSAT CHECKING
    check_continue_conditions([]).
    check_continue_conditions([symbol('continue-if-sat'), symbol('unsat') | _]) :-
        fail.
    check_continue_conditions([symbol('continue-if-sat'), symbol('unknow') | _]) :-
        fail.
    check_continue_conditions([string('continue-if-sat'), symbol('unsat') | _]) :-
        fail.
    check_continue_conditions([string('continue-if-sat'), symbol('unknow') | _]) :-
        fail.
    check_continue_conditions([symbol('continue-if-unsat'), symbol('sat') | _]) :-
        fail.
    check_continue_conditions([symbol('continue-if-unsat'), symbol('unknow') | _]) :-
        fail.
    check_continue_conditions([string('continue-if-unsat'), symbol('sat') | _]) :-
        fail.
    check_continue_conditions([string('continue-if-unsat'), symbol('unknow') | _]) :-
        fail.
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
        atom_chars(Str, Chars),
        remove_parentheses(Chars, WithoutParentheses),
        split_by_space(WithoutParentheses, Atoms),
        map_atoms_to_symbols(Atoms, Symbols).
    normalize_constraint_symbols(Symbols, Symbols) :-
        is_list_ISO(Symbols),
        map_atoms_to_symbols(Symbols, Symbols).

    % Map a list of atoms to a list of symbols
    map_atoms_to_symbols([], []).
    map_atoms_to_symbols([Atom|Atoms], [symbol(Atom)|Symbols]) :-
        map_atoms_to_symbols(Atoms, Symbols).
    
        
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


    % Extract last Model
    extract_last_model(Expressions, LastModel) :-
        reverse(Expressions, ReversedExpressions),
        extract_model(ReversedExpressions, LastModel).

    % Remove the symbol(model) added by some solver in the model
    clean_model([symbol(model) | Rest], CleanModel) :-
        !, CleanModel = Rest.
    clean_model(Model, Model).
    
    % Extract Model in expression List
    extract_model([Model | _], CleanModel) :-
        is_list_ISO(Model),
        clean_model(Model, CleanModel),
        \+ (CleanModel = [symbol(_) | _]),
        \+ (CleanModel = [string(_) | _]).
    extract_model([_ | Rest], Model) :-
        extract_model(Rest, Model).
    
    % Find the FunName in the Model
    find_value_in_model(FunName, [VarDefinition | _], Value) :-
        VarDefinition = [_, symbol(FunName), _, _, TypedValue],
        extract_value(TypedValue, Value).
    find_value_in_model(FunName, [_ | Rest], Value) :-
        find_value_in_model(FunName, Rest, Value).
    
    % Separate the Value from the functor of the type (e.g., numeral(Value)).
    extract_value(TypedValue, Value) :-
        TypedValue =.. [_Type, Value].
    
% UTILS
    % Transform array [x,y,z] to string "(x y z)"
    list_symbols_to_string(List, Result) :-
        symbols_to_string(List, InnerResult),
        atom_concat('(', InnerResult, TempResult),
        atom_concat(TempResult, ')', Result).

    symbols_to_string([], '').
    symbols_to_string([Symbol], String) :-
        term_to_string(Symbol, String).
    symbols_to_string([Symbol|Rest], Result) :-
        term_to_string(Symbol, SymbolString),
        symbols_to_string(Rest, RestString),
        atom_concat(SymbolString, ' ', TempResult),
        atom_concat(TempResult, RestString, Result).

    term_to_string(Term, String) :-
        term_to_string_helper(Term, Chars),
        atom_chars(String, Chars).        

     % Transform string "[x,y]" to array [x,y]
     string_to_list_symbols(String, List) :-
        atom_concat('(', Rest, String),
        atom_concat(SymbolsString, ')', Rest),
        read_term(SymbolsString, List, [syntax_errors(quiet)]).

    % Convert an atom to a number
    atom_to_number(Atom, Number) :-
        atom_chars(Atom, Chars),
        number_chars(Number, Chars).

    % Convert a number to an atom
    number_to_atom(Number, Atom) :-
        number_chars(Number, Chars),
        atom_chars(Atom, Chars).

    % Transformation en symbol
    smt_symbol(X, symbol(S)) :- atom(X), !, S = X.
    smt_symbol(X, X).

    convert_to_symbols([], []).
    convert_to_symbols([H|T], [symbol(H)|ConvertedT]) :-
            atomic(H), !,
            convert_to_symbols(T, ConvertedT).
    convert_to_symbols([H|T], [ConvertedH|ConvertedT]) :-
            is_list_ISO(H),
            convert_to_symbols(H, ConvertedH),
            convert_to_symbols(T, ConvertedT).

    %is_list
    is_list_ISO(X) :- nonvar(X), X = [].
    is_list_ISO(X) :- nonvar(X), X = [_|_].


    term_to_string_helper(Var, Chars) :-
        var(Var), !,
        atom_chars(Var, Chars).
    term_to_string_helper(Atom, Chars) :-
        atom(Atom), !,
        atom_chars(Atom, Chars).
    term_to_string_helper(Number, Chars) :-
        number(Number), !,
        number_chars(Number, Chars).
    term_to_string_helper(Compound, Chars) :-
        compound(Compound),
        Compound =.. [Functor|Args],
        term_to_string_helper(Functor, FunctorChars),
        term_to_string_list(Args, ArgsChars),
        append(FunctorChars, ArgsChars, Chars).
    
    term_to_string_list([], []).
    term_to_string_list([H|T], Chars) :-
        term_to_string_helper(H, HChars),
        term_to_string_list(T, TChars),
        append(HChars, TChars, Chars).

    % Remove the opening and closing parentheses
    remove_parentheses(['('|T], WithoutParentheses) :-
        reverse(T, [_|ReversedWithoutClosing]),
        reverse(ReversedWithoutClosing, WithoutParentheses).

    % Split a list of characters by spaces
    split_by_space(Chars, Atoms) :-
        split_by_space_helper(Chars, [], Atoms).

    split_by_space_helper([], Current, [Atom]) :-
        atom_chars(Atom, Current).
    split_by_space_helper([' '|T], Current, [Atom|Rest]) :-
        atom_chars(Atom, Current),
        split_by_space_helper(T, [], Rest).
    split_by_space_helper([H|T], Current, Atoms) :-
        split_by_space_helper(T, [H|Current], Atoms).
