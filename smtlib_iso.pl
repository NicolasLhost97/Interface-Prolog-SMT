/**
  * 
  * FILENAME: smtlib.pl
  * DESCRIPTION: This module contains predicates for parsing SMT-LIB programs.
  * AUTHORS: José Antonio Riaza Valverde <riaza.valverde@gmail.com>
  * GITHUB: https://github.com/jariazavalverde/prolog-smtlib
  * UPDATED: 20.01.2019
  * 
  **/



% :- module(smtlib, [
%     % read from file
%     smtlib_read_expression/2,
%     smtlib_read_expressions/2,
%     smtlib_read_theory/2,
%     smtlib_read_logic/2,
%     smtlib_read_script/2,
%     % read from chars
%     smtlib_parse_expression/2,
%     smtlib_parse_expressions/2,
%     smtlib_parse_theory/2,
%     smtlib_parse_logic/2,
%     smtlib_parse_script/2,
%     % write
%     smtlib_write_to_stream/2,
%     smtlib_write_to_file/2
% ]).



/**
  * 
  * Barrett, Clark, Aaron Stump, and Cesare Tinelli. "The smt-lib standard: Version 2.0."
  * Proceedings of the 8th International Workshop on Satisfiability Modulo Theories (Edinburgh, England).
  * Vol. 13. 2010.
  * 
  * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf
  * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
  * 
  **/



% EXPORTED PREDICATES

% smtlib_read_expression/2
% smtlib_read_expression(+Path, ?Expression)
%
% This predicate succeeds when file +Path exists and ?Expression
% is the expression resulting from parsing the file as an
% S-Expression of SMT-LIB.
smtlib_read_expression(Path, Expression) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    smtlib_parse_expression(Chars, Expression).

% smtlib_read_expressions/2
% smtlib_read_expressions(+Path, ?Expression)
%
% This predicate succeeds when file +Path exists and ?Expression
% is the expression resulting from parsing the file as a list of
% S-Expressions of SMT-LIB.
smtlib_read_expressions(Path, Expression) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    smtlib_parse_expressions(Chars, Expression).

% smtlib_read_theory/2
% smtlib_read_theory(+Path, ?Theory)
%
% This predicate succeeds when file +Path exists and ?Theory
% is the expression resulting from parsing the file as an
% SMT-LIB theory declaration.
smtlib_read_theory(Path, Theory) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    smtlib_parse_theory(Chars, Theory).

% smtlib_read_logic/2
% smtlib_read_logic(+Path, ?Logic)
%
% This predicate succeeds when file +Path exists and ?Theory
% is the expression resulting from parsing the file as an
% SMT-LIB logic declaration.
smtlib_read_logic(Path, Logic) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    smtlib_parse_logic(Chars, Logic).

% smtlib_read_script/2
% smtlib_read_script(+Chars, ?Script)
%
% This predicate succeeds when file +Path exists and ?Script is
% the script resulting from parsing +Chars as an SMT-LIB script.
smtlib_read_script(Path, Script) :-
    open(Path, read, Stream),
    stream_to_list(Stream, Chars),
    close(Stream),
    smtlib_parse_script(Chars, Script).

% smtlib_parse_expression/2
% smtlib_parse_expression(+Chars, ?Expression)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Expression is the expression resulting from parsing +Chars as an
% S-Expression of SMT-LIB.
smtlib_parse_expression(Chars, Expression) :- s_expr(Expression, Chars, []).

% smtlib_parse_expressions/2
% smtlib_parse_expressions(+Chars, ?Expression)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Expression is the expression resulting from parsing +Chars as a
% list of S-Expressions of SMT-LIB.
smtlib_parse_expressions(Chars, Expression) :- s_exprs(Expression, Chars, []).

% smtlib_parse_theory/2
% smtlib_parse_theory(+Chars, ?Theory)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Theory is the expression resulting from parsing +Chars as an
% SMT-LIB theory declaration.
smtlib_parse_theory(Chars, Theory) :- theory_decl(Theory, Chars, []).

% smtlib_parse_logic/2
% smtlib_parse_logic(+Chars, ?Logic)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Logic is the expression resulting from parsing +Chars as an
% SMT-LIB logic declaration.
smtlib_parse_logic(Chars, Logic) :- logic(Logic, Chars, []).

% smtlib_parse_script/2
% smtlib_parse_script(+Chars, ?Script)
%
% This predicate succeeds when +Chars is a list of characters and
% ?Script is the script resulting from parsing +Chars as an SMT-LIB script.
smtlib_parse_script(Chars, Script) :- script(Script, Chars, []).

% smtlib_write_to_stream/2
% smtlib_write_to_stream(+Stream, +SMTLIB)
%
% This predicate succeeds when +SMTLIB is a valid SMT-LIB
% expression and can be written in the stream +Stream.
smtlib_write_to_stream(Stream, numeral(N)) :- !, write(Stream, N), write(Stream, ' ').
smtlib_write_to_stream(Stream, decimal(D)) :- !, write(Stream, D), write(Stream, ' ').
smtlib_write_to_stream(Stream, hexadecimal(H)) :- !, write(Stream, H), write(Stream, ' ').
smtlib_write_to_stream(Stream, binary(B)) :- !, write(Stream, B), write(Stream, ' ').
smtlib_write_to_stream(Stream, symbol(S)) :- !, write(Stream, S), write(Stream, ' ').
smtlib_write_to_stream(Stream, reserved(R)) :- !, write(Stream, R), write(Stream, ' ').
smtlib_write_to_stream(Stream, keyword(K)) :- !, write(Stream, ':'), write(Stream, K), write(Stream, ' ').
smtlib_write_to_stream(Stream, string(S)) :- !,
    write(Stream, '"'),
    write(Stream, S),
    write(Stream, '"'),
    write(Stream, ' ').
smtlib_write_to_stream(Stream, list(Expr)) :- !,
    maplist_ISO(smtlib_write_to_stream(Stream), Expr).
smtlib_write_to_stream(Stream, Expr) :-
    is_list_ISO(Expr), !,
    write(Stream, '('),
    maplist_ISO(smtlib_write_to_stream(Stream), Expr),
    writeln_ISO(Stream, ')').

% smtlib_write_to_file/2
% smtlib_write_to_file(+Path, +SMTLIB)
%
% This predicate succeeds when +SMTLIB is a valid SMT-LIB
% expression and can be written in the file +Path.
smtlib_write_to_file(Path, SMTLIB) :- 
    open(Path, write, Stream),
    smtlib_write_to_stream(Stream, SMTLIB),
    close(Stream).



% UTILS

% stream_to_list/2
% stream_to_list(+Stream, ?List)
%
% This predicate succeeds when ?List is the lists
% of characters reads from the stream +Stream.
stream_to_list(Stream, []) :-
    at_end_of_stream(Stream), !.
stream_to_list(Stream, [Char|Input]) :-
    get_code(Stream, Code),
    char_code(Char, Code),
stream_to_list(Stream, Input).



% LEXICON
% SMT-LIB source files consist of ASCII characters.

% A comment is any character sequence not contained within a string literal
% or a quoted symbol that begins with the semicolon character ; and ends 
% with the first subsequent line-breaking character.
comment --> [X], {X \= '\n'}, !, comment.
comment --> [].

% Comments together with the space, tab and line-breaking characters are all
% considered whitespace.
whitespace --> [' '].
whitespace --> ['\t'].
whitespace --> ['\n'].
whitespace --> ['\r'].
whitespace --> [';'], comment, ['\n'], !.
whitespace([';'|Xs],[]) :- comment(Xs,[]).

whitespaces --> whitespace, !, whitespaces.
whitespaces --> [].

lpar --> ['('], whitespaces.
rpar --> [')'], whitespaces.

% A <numeral> is the digit 0 or a non-empty sequence of digits not starting with 0.
numeral(numeral(Y)) --> digits([X|Xs]), {(Xs = [] ; X \= '0'), number_chars(Y, [X|Xs])}, whitespaces.

numerals([X|Xs]) --> numeral(X), !, numerals(Xs).
numerals([]) --> [].

digits([X|Xs]) --> [X], {char_code(X, C), C >= 48, C =< 57}, !, digits(Xs).
digits([]) --> [].

% A <decimal> is a token of the form <numeral>.0*<numeral>.
decimal(decimal(D)) -->
    digits([X|Xs]),
    {(Xs = [] ; X \= '0')},
    ['.'], digits(Y),
    {append([X|Xs], ['.'|Y], Z),
    number_chars(D, Z)},
    whitespaces.

% A <hexadecimal> is a non-empty case-insensitive sequence of digits and letters
% from A to F preceded by the (case sensitive) characters #x.
hexadecimal(hexadecimal(Y)) --> ['#','x'], hexadecimal_digits(X), {X \= [], atom_chars(Y, X)}, whitespaces.

hexadecimal_digits([X|Xs]) --> [X],
    {member(X, ['0','1','2','3','4','5','6','7','8','9',a,b,c,d,e,f,'A','B','C','D','E','F'])}, !,
    hexadecimal_digits(Xs).
hexadecimal_digits([]) --> [].

% A <binary> is a non-empty sequence of the characters 0 and 1 preceded by the characters #b.
binary(binary(Y)) --> ['#','b'], binary_digits(X), {X \= [], atom_chars(Y, X)}, whitespaces.

binary_digits([X|Xs]) --> [X], {member(X, ['0','1'])}, !, binary_digits(Xs).
binary_digits([]) --> [].

% A <string> is any sequence of printable ASCII characters delimited by double quotes
% (") and possibly containing the C-style escape sequences \" and \\, both of which are
% treated as a single character—respectively " and \.  The first escape sequence allows
% as usual the double quote character to appear within a string literal, the second allows
% the backslash character to end a string literal.
string(string(Y)) --> ['"'], quoted(X), ['"'], {atom_chars(Y, X)}, whitespaces.

quoted([X|Xs]) --> printable_character(X), {X \= '"'}, !, quoted(Xs).
quoted([X|Xs]) --> [X], {member(X, [' ','\n','\r','\t'])}, !, quoted(Xs).
quoted(['"'|Xs]) --> ['"','"'], !, quoted(Xs).
quoted([]) --> [].

printable_character(X) --> [X], {char_code(X, C), (C >= 32, C =< 126 ; C >= 128)}.

% The language uses a number of reserved words, sequences of (non-whitespace) characters
% that are to be treated as individual tokens. Additionally, each command name in the
% scripting language is also a reserved word.
reserved_word(X) :- member(X, [
    par, 'BINARY', 'HEXADECIMAL', 'NUMERAL', 'DECIMAL', 'STRING', '_', '!', as,
    let, forall, exists, match, 'set-logic', 'set-option', 'set-info', 'declare-sort',
    'define-sort', 'declare-fun', push, pop, assert, 'check-sat', 'get-assertions',
    'get-proof', 'get-unsat-core', 'get-value', 'get-assignment', 'get-info', exit,
    'check-sat-assuming', 'declare-const', 'declare-datatype', 'declare-datatypes',
    'define-fun', 'define-fun-rec', 'define-funs-rec', echo, 'get-model', 'get-option',
    'get-unsat-assumptions', reset, 'reset-assertions', 'set-option'
]).

reserved_word(reserved(Y)) -->
    symbol_chars([X|Xs]),
    {atom_chars(Y, [X|Xs]),
    reserved_word(Y)},
    whitespaces.

% A <symbol> is either a simple symbol or a quoted symbol. The former is any non-empty
% sequence of letters, digits and the characters ~ ! @ $ % ^ & * _ - + = < > . ? / that
% does not start with a digit and is not a reserved word. The latter is any sequence of
% printable ASCII characters (including space, tab, and line-breaking characters) except
% for the backslash character \, that starts and ends with | and does not otherwise contain |.
symbol(X) --> simple_symbol(X).
symbol(X) --> quoted_symbol(X).

symbols([X|Xs]) --> symbol(X), !, symbols(Xs).
symbols([]) --> [].

simple_symbol(symbol(Y)) -->
    symbol_chars([X|Xs]),
    {\+member(X, ['0','1','2','3','4','5','6','7','8','9']),
    atom_chars(Y, [X|Xs]),
    \+reserved_word(Y)},
    whitespaces.

symbol_chars([X|Xs]) --> [X],
    {member(X, ['~','!','@','$','%','^','&','*','_','-','+','=','<','>','.','?','/']) ;
    (char_code(X, C), C >= 48, C =< 57) ; 
    (char_code(X, C), C >= 97, C =< 122) ; 
    (char_code(X, C), C >= 65, C =< 90)}, !,
    symbol_chars(Xs).
symbol_chars([]) --> [].

quoted_symbol(symbol(Y)) --> ['|'], quoted_symbol_chars(X), ['|'], {atom_chars(Y, X)}, whitespaces.

quoted_symbol_chars([X|Xs]) --> printable_character(X), {X \= ('|'), X \= ('\\')}, !, quoted_symbol_chars(Xs).
quoted_symbol_chars([X|Xs]) --> [X], {member(X, [' ','\n','\r','\t'])}, !, quoted_symbol_chars(Xs).
quoted_symbol_chars([]) --> [].

% A <keyword> is a non-empty sequence of letters, digits, and the characters
% ~ ! @ $ % ^ & * _ - + = < > . ? / preceded by the character :.
keyword(keyword(Y)) --> [':'], symbol_chars(X), {X \= [], atom_chars(Y, X)}, whitespaces.



% S-EXPRESSIONS

% An S-expression is either a non-parenthesis token or a (possibly  empty) sequence of
% S-expressions enclosed in parentheses. Every syntactic category of the SMT-LIB language
% is a specialization of the category <s-expr> defined by the production rules below.
spec_constant(X) --> decimal(X), !.
spec_constant(X) --> numeral(X), !.
spec_constant(X) --> hexadecimal(X), !.
spec_constant(X) --> binary(X), !.
spec_constant(X) --> string(X), !.

s_expr(X) --> whitespaces, s_expr2(X).
s_expr2(X) --> spec_constant(X), !.
s_expr2(X) --> symbol(X), !.
s_expr2(X) --> reserved_word(X), !.
s_expr2(X) --> keyword(X), !.
s_expr2(X) --> lpar, s_exprs(X), whitespaces, rpar.

s_exprs([X|Xs]) --> s_expr(X), !, s_exprs(Xs).
s_exprs([]) --> [].



% IDENTIFIERS

% Indexed identifiers are defined more systematically as the application of the reserved
% word _ to a symbol and one or more indices. Indices can be numerals or symbols.
identifier([reserved('_'),X|Xs]) --> lpar, ['_'], whitespaces, symbol(X), indices(Xs), {Xs \= []}, rpar.
identifier(X) --> symbol(X).

index(X) --> numeral(X).
index(X) --> symbol(X).

indices([X|Xs]) --> index(X), !, indices(Xs).
indices([]) --> [].


% ATTRIBUTES

% These are generally pairs consisting of an attribute name and an associated value,
% although attributes with no value are also allowed.
attribute_value(X) --> spec_constant(X), !.
attribute_value(X) --> symbol(X), !.
attribute_value(Xs) --> lpar, s_exprs(Xs), rpar.

attribute([X,Xs]) --> keyword(X), attribute_value(Xs), !.
attribute(X) --> keyword(X).

attributes([X|Xs]) --> attribute(X), !, attributes(Xs).
attributes([]) --> [].


% SORTS

% A sort symbol can be either the distinguished symbol Bool or any <identifier>. A sort
% parameter can be any <symbol> (which in turn, is an <identifier>).
sort([X|Xs]) --> lpar, identifier(X), sorts(Xs), {Xs \= []}, rpar.
sort(X) --> identifier(X).

sorts([X|Xs]) --> sort(X), sorts(Xs).
sorts([]) --> [].



% TERMS AND FORMULAS

% Well-sorted terms are a subset of the set of all terms. The latter are constructed out of
% constant symbols in the <spec-constant> category (numerals, rationals, strings, etc.),
% variables, function symbols, three kinds of binders--the reserved words let, forall, match
% and exists--and an annotation operator--the reserved word !.
qual_identifier(X) --> identifier(X).
qual_identifier([reserved(as),X,Y]) --> lpar, [a,s], whitespaces, identifier(X), sort(Y), rpar.

var_binding([X,Y]) --> lpar, symbol(X), term(Y), rpar.
var_bindings([X|Xs]) --> var_binding(X), !, var_bindings(Xs).
var_bindings([]) --> [].

sorted_var([X,Y]) --> lpar, symbol(X), sort(Y), rpar.
sorted_vars([X|Xs]) --> sorted_var(X), !, sorted_vars(Xs).
sorted_vars([]) --> [].

pattern([X|Xs]) --> lpar, !, symbol(X), symbols(Xs), {Xs \= []}, rpar.
pattern(X) --> symbol(X).

match_case([X,Y]) --> lpar, pattern(X), term(Y), rpar.
match_cases([X|Xs]) --> match_case(X), !, match_cases(Xs).
match_cases([]) --> [].

term(X) --> spec_constant(X).
term(X) --> qual_identifier(X).
term([X|Xs]) --> lpar, qual_identifier(X), terms(Xs), {Xs \= []}, rpar.
term([reserved(let), Xs, X]) --> lpar, reserved_word(reserved(let)), lpar, var_bindings(Xs), {Xs \= []}, rpar, term(X), rpar.
term([reserved(Y), Xs, X]) --> lpar, reserved_word(reserved(Y)), {member(Y, [forall, exists])}, lpar, sorted_vars(Xs), {Xs \= []}, rpar, term(X), rpar.
term([reserved(match), Xs]) --> lpar, reserved_word(reserved(match)), lpar, match_cases(Xs), {Xs \= []}, rpar, rpar.
term([reserved('!'),X|Xs]) --> lpar, reserved_word(reserved('!')), term(X), attributes(Xs), {Xs \= []}, rpar.

terms([X|Xs]) --> term(X), !, terms(Xs).
terms([]) --> [].



% THEORY DECLARATIONS

% The syntax of theory declarations follows an attribute-value-based format. A theory
% declaration consists of a theory name and a list of <attribute> elements. Theory attributes
% with the following predefined keywords have a prescribed usage and semantics: :definition,
% :funs, :funs-description, :notes, :sorts, :sorts-description, and :values. Additionally, a
% theory declaration can contain any number of user-defined attributes.
sort_symbol_decl([X,Y|Z]) --> lpar, identifier(X), numeral(Y), attributes(Z), rpar.
sort_symbol_decls([X|Xs]) --> sort_symbol_decl(X), !, sort_symbol_decls(Xs).
sort_symbol_decls([]) --> [].

meta_spec_constant(reserved(X)) --> reserved_word(reserved(X)), {member(X, ['NUMERAL','DECIMAL','STRING'])}.

fun_symbol_decl([X,Y|Z]) --> lpar, spec_constant(X), sort(Y), attributes(Z), rpar.
fun_symbol_decl([X,Y|Z]) --> lpar, meta_spec_constant(X), sort(Y), attributes(Z), rpar.
fun_symbol_decl([X|YZ]) --> lpar, identifier(X), sorts(Y), {Y \= []}, attributes(Z), rpar, {append(Y, Z, YZ)}.

par_fun_symbol_decl(X) --> fun_symbol_decl(X).
par_fun_symbol_decl([reserved(par), X, [Y|ZW]]) -->
    lpar, reserved_word(reserved(par)),
    lpar, symbols(X), {X \= []}, rpar,
    lpar, identifier(Y), sorts(Z), {Z \= []},
    attributes(W), rpar,
    rpar, {append(Z, W, ZW)}.

par_fun_symbol_decls([X|Xs]) --> par_fun_symbol_decl(X), !, par_fun_symbol_decls(Xs).
par_fun_symbol_decls([]) --> [].

theory_attribute([keyword(sorts),Xs]) -->  keyword(keyword(sorts)), lpar, sort_symbol_decls(Xs), {Xs \= []}, rpar, !.
theory_attribute([keyword(funs),Xs]) -->  keyword(keyword(funs)), lpar, par_fun_symbol_decls(Xs), {Xs \= []}, rpar, !.
theory_attribute([keyword(X),Y]) -->  keyword(keyword(X)), {member(X,['sorts-description','funs-description',definition,values,notes])}, string(Y), !.
theory_attribute(X) -->  attribute(X), !.

theory_attributes([X|Xs]) --> theory_attribute(X), !, theory_attributes(Xs).
theory_attributes([]) --> [].

theory_decl(list([symbol(theory),X|Y])) --> whitespaces, lpar, symbol(symbol(theory)), symbol(X), theory_attributes(Y), {Y \= []}, rpar.



% LOGIC DECLARATIONS

% Attributes with the following predefined keywords have a prescribed usage and semantics
% in logic declarations: :theories, :language, :extensions, :notes, and :values. Additionally,
% as with theories, a logic declaration can contain any number of user-defined  attributes.
logic_attribute([keyword(theories),Xs]) --> keyword(keyword(theories)), lpar, symbols(Xs), {Xs \= []}, rpar, !.
logic_attribute([keyword(X),Y]) --> keyword(keyword(X)), {member(X,[language,extensions,values,notes])}, string(Y), !.
logic_attribute(X) --> attribute(X).

logic_attributes([X|Xs]) --> logic_attribute(X), !, logic_attributes(Xs).
logic_attributes([]) --> [].

logic(list([symbol(logic),X|Xs])) --> whitespaces, lpar, symbol(symbol(logic)), symbol(X), logic_attributes(Xs), {Xs \= []}, rpar.



% SCRIPTS

% Scripts are sequences of commands. In line with the LISP-like syntax, all commands look
% like LISP-function applications, with a command name applied to zero or more arguments.

sort_dec([X,Y]) --> lpar, symbol(X), numeral(Y), rpar.
sort_decs([X|Xs]) --> sort_dec(X), !, sort_decs(Xs).
sort_decs([]) --> [].

selector_dec([X,Y]) --> lpar, symbol(X), sort(Y), rpar.
selector_decs([X|Xs]) --> selector_dec(X), !, selector_decs(Xs).
selector_decs([]) --> [].

constructor_dec([X|Xs]) --> lpar, symbol(X), selector_decs(Xs), rpar.
constructor_decs([X|Xs]) --> constructor_dec(X), !, constructor_decs(Xs).
constructor_decs([]) --> [].

datatype_dec(Xs) --> lpar, constructor_decs(Xs), {Xs \= []}, rpar.
datatype_dec([reserved(par),X,Y]) --> lpar, reserved_word(reserved(par)),
    lpar, symbols(X), {X \= []}, rpar,
    lpar, constructor_decs(Y), {Y \= []}, rpar, rpar.
datatype_decs([X|Xs]) --> datatype_dec(X), !, datatype_decs(Xs).
datatype_decs([]) --> [].

function_dec([X,Y,Z]) --> lpar, symbol(X), lpar, sorted_vars(Y), rpar, sort(Z), rpar.
function_decs([X|Xs]) --> function_dec(X), !, function_decs(Xs).
function_decs([]) --> [].

function_def([X,Y,Z,W]) --> symbol(X), lpar, sorted_vars(Y), rpar, sort(Z), term(W).

prop_literal([symbol(not),X]) --> lpar, symbol(symbol(not)), symbol(X), rpar.
prop_literal(X) --> symbol(X).
prop_literals([X|Xs]) --> prop_literal(X), !, prop_literals(Xs).
prop_literals([]) --> [].

command([reserved('check-sat-assuming'),X]) --> lpar, reserved_word(reserved('check-sat-assuming')), lpar, prop_literals(X), rpar, rpar.
command([reserved('declare-const'),X,Y]) --> lpar, reserved_word(reserved('declare-const')), symbol(X), sort(Y), rpar.
command([reserved('declare-datatype'),X,Y]) --> lpar, reserved_word(reserved('declare-datatype')), symbol(X), datatype_dec(Y), rpar.
command([reserved('declare-datatypes'),X,Y]) --> lpar, reserved_word(reserved('declare-datatypes')),
    lpar, sort_decs(X), rpar, lpar, lpar, datatype_decs(Y), {length(X,Length), length(Y,Length), Length > 0}, rpar, rpar, rpar.
command([reserved('set-logic'),X]) --> lpar, reserved_word(reserved('set-logic')), symbol(X), rpar.
command([reserved('set-option')|X]) --> lpar, reserved_word(reserved('set-option')), option(X), rpar.
command([reserved('set-info'),X]) --> lpar, reserved_word(reserved('set-info')), attribute(X), rpar.
command([reserved('declare-sort'),X,Y]) --> lpar, reserved_word(reserved('declare-sort')), symbol(X), numeral(Y), rpar.
command([reserved('define-sort'),X,Y,Z]) --> lpar, reserved_word(reserved('define-sort')), symbol(X), lpar, symbols(Y), rpar, sort(Z), rpar.
command([reserved('declare-fun'),X,Y,Z]) --> lpar, reserved_word(reserved('declare-fun')), symbol(X), lpar, sorts(Y), rpar, sort(Z), rpar.
command([reserved('define-fun'),X,Y,Z,W]) --> lpar, reserved_word(reserved('define-fun')), function_def([X,Y,Z,W]), rpar.
command([reserved('define-fun-rec'),X,Y,Z,W]) --> lpar, reserved_word(reserved('define-fun-rec')), function_def([X,Y,Z,W]), rpar.
command([reserved('define-funs-rec'),X,Y]) --> lpar, reserved_word(reserved('define-funs-rec')),
    lpar, function_decs(X), rpar, lpar, terms(Y), {length(X,Length), length(Y,Length), Length > 0}, rpar, rpar.
command([reserved(push),X]) --> lpar, reserved_word(reserved(push)), numeral(X), rpar.
command([reserved(pop),X]) --> lpar, reserved_word(reserved(pop)), numeral(X), rpar.
command([reserved(assert),X]) --> lpar, reserved_word(reserved(assert)), term(X), rpar.
command([reserved(X)]) --> lpar, reserved_word(reserved(X)), {member(X,['check-sat','get-model','get-assertions','get-proof','get-unsat-core','get-assignment','get-unsat-assumptions',exit,reset,'reset-assertions'])}, rpar.
command([reserved('get-value'),Xs]) --> lpar, reserved_word(reserved('get-value')), lpar, terms(Xs), {Xs \= []}, rpar, rpar.
command([reserved('get-option'),X]) --> lpar, reserved_word(reserved('get-option')), keyword(X), rpar.
command([reserved('get-info'),X]) --> lpar, reserved_word(reserved('get-info')), info_flag(X), rpar.
command([reserved(echo),X]) --> lpar, reserved_word(reserved(echo)), string(X), rpar.

script(list(X)) --> whitespaces, script2(X).
script2([X|Xs]) --> command(X), !, script2(Xs).
script2([]) --> [].

% The command set-option takes as argument expressions of the syntactic category <option>
% which have the same form as attributes with values. Options with the predefined keywords
% below have a prescribed usage and semantics.
b_value(symbol(X)) --> symbol(symbol(X)), {member(X, [true,false])}.

option([keyword(X),Y]) --> keyword(keyword(X)), {member(X,['global-declarations','print-success','interactive-mode','produce-proofs','produce-unsat-cores','produce-models','produce-assignments','produce-assertions','produce-unsat-assumptions'])}, b_value(Y).
option([keyword('diagnostic-output-channel'),X]) --> keyword(keyword('diagnostic-output-channel')), string(X).
option([keyword('random-seed'),X]) --> keyword(keyword('random-seed')), numeral(X).
option([keyword('verbosity'),X]) --> keyword(keyword('verbosity')), numeral(X).
option([keyword('reproducible-resource-limit'),X]) --> keyword(keyword('reproducible-resource-limit')), numeral(X).
option([keyword('regular-output-channel'),X]) --> keyword(keyword('regular-output-channel')), string(X).
option([X]) --> attribute(X).

% The command get-info takes as argument expressions of the syntactic category <info_flag>
% which are flags with the same form as keywords. The predefined flags below have a prescribed
% usage and semantics.
info_flag(keyword(X)) --> keyword(keyword(X)), {member(X,['error-behavior',name,authors,version,'reason-unknown','all-statistics','assertion-stack-lavels'])}, !.
info_flag(X) --> keyword(X).


% ISO-Prolog
maplist_ISO(_, []).
maplist_ISO(Goal, [H|T]) :-
    arg(1, Goal, Stream),
    GoalWithArg =.. [smtlib_write_to_stream, Stream, H],
    call(GoalWithArg),
    maplist_ISO(Goal, T).

is_list_ISO(X) :- nonvar(X), X = [].
is_list_ISO(X) :- nonvar(X), X = [_|_].

writeln_ISO(Stream, Text) :-
    write(Stream, Text),
    nl(Stream).