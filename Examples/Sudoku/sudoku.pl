:- consult(interfaceCopy).
:- use_module(library(clpfd)).

%%%%%%%%%%%%%%%%%%%%%%%
%%%% SUDOKU PROLOG %%%%
%%%%%%%%%%%%%%%%%%%%%%%

sudoku(Rows) :-
    length(Rows, 9), maplist(same_length(Rows), Rows),
    append(Rows, Vs), Vs ins 1..9,
    maplist(all_distinct, Rows),
    transpose(Rows, Columns),
    maplist(all_distinct, Columns),
    Rows = [As,Bs,Cs,Ds,Es,Fs,Gs,Hs,Is],
    blocks(As, Bs, Cs),
    blocks(Ds, Es, Fs),
    blocks(Gs, Hs, Is),
    labeling([],Vs).

blocks([], [], []).
blocks([N1,N2,N3|Ns1], [N4,N5,N6|Ns2], [N7,N8,N9|Ns3]) :-
    all_distinct([N1,N2,N3,N4,N5,N6,N7,N8,N9]),
    blocks(Ns1, Ns2, Ns3).

problem(1, [[_,_,_,_,_,_,_,_,_],
            [_,_,_,_,_,3,_,8,5],
            [_,_,1,_,2,_,_,_,_],
            [_,_,_,5,_,7,_,_,_],
            [_,_,4,_,_,_,1,_,_],
            [_,9,_,_,_,_,_,_,_],
            [5,_,_,_,_,_,_,7,3],
            [_,_,2,_,1,_,_,_,_],
            [_,_,_,_,4,_,_,_,9]]).

% Exemple de grille Sudoku à résoudre
problem(2, [[8,_,_,_,_,_,_,_,_],
            [_,_,3,6,_,_,_,_,_],
            [_,7,_,_,9,_,2,_,_],
            [_,5,_,_,_,7,_,_,_],
            [_,_,_,_,4,5,7,_,_],
            [_,_,_,1,_,_,_,3,_],
            [_,_,1,_,_,_,_,6,8],
            [_,_,8,5,_,_,_,1,_],
            [_,9,_,_,_,_,4,_,_]]).

% Utilisation :
% ?- problem(1, Puzzle), solve_sudoku(Puzzle), print_sudoku(Puzzle).

sudoku_prolog():-
    problem(1, Rows),
    sudoku(Rows), 
    maplist(portray_clause, Rows).
% 700,213 inferences, 0.082 CPU in 0.083 seconds (98% CPU, 8556505 Lips)

hardest_sudoku_prolog():-
    problem(2, Rows),
    sudoku(Rows), 
    maplist(portray_clause, Rows).
% NE TROUVE PAS
% 400,787 inferences, 0.050 CPU in 0.051 seconds (98% CPU, 7988260 Lips)


%%%%%%%%%%%%%%%%%%%%%%%
%%%% SUDOKU SMTLIB %%%%
%%%%%%%%%%%%%%%%%%%%%%%

sudoku_smt():-
    smt_load_file('sudoku.smt2',[], SudokuScript),
    % Row 0
    % Row 1
    smt_parse('(assert (= (board 1 5) V3))',C1),
    smt_parse('(assert (= (board 1 7) V8))',C2),
    smt_parse('(assert (= (board 1 8) V5))',C3),
    % Row 2
    smt_parse('(assert (= (board 2 2) V1))',C4),
    smt_parse('(assert (= (board 2 4) V2))',C5),
    % Row 3
    smt_parse('(assert (= (board 3 3) V5))',C6),
    smt_parse('(assert (= (board 3 5) V7))',C7),
    % Row 4
    smt_parse('(assert (= (board 4 2) V4))',C8),
    smt_parse('(assert (= (board 4 6) V1))',C9),
    % Row 5
    smt_parse('(assert (= (board 5 1) V9))',C10),
    % Row 6
    smt_parse('(assert (= (board 6 0) V5))',C11),
    smt_parse('(assert (= (board 6 7) V7))',C12),
    smt_parse('(assert (= (board 6 8) V3))',C13),
    % Row 7
    smt_parse('(assert (= (board 7 2) V2))',C14),
    smt_parse('(assert (= (board 7 4) V1))',C15),
    % Row 8
    smt_parse('(assert (= (board 8 4) V4))',C16),
    smt_parse('(assert (= (board 8 8) V9))',C17),

    SimpleSudoku = [list(SudokuScript), C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17],
    smt_load_file('sudoku_show_values.smt2',SimpleSudoku, Script),
    smt_solve_z3(Script,_).
% 323,693 inferences, 0.040 CPU in 1.122 seconds (4% CPU, 7998147 Lips)

hardest_sudoku_smt():-
    smt_load_file('sudoku.smt2',[], SudokuScript),
    % Row 0
    smt_parse('(assert (= (board 0 0) V8))',C1),
    % Row 1
    smt_parse('(assert (= (board 1 2) V3))',C2),
    smt_parse('(assert (= (board 1 3) V6))',C3),
    % Row 2
    smt_parse('(assert (= (board 2 1) V7))',C4),
    smt_parse('(assert (= (board 2 4) V9))',C5),
    smt_parse('(assert (= (board 2 6) V2))',C6),
    % Row 3
    smt_parse('(assert (= (board 3 1) V5))',C7),
    smt_parse('(assert (= (board 3 5) V7))',C8),
    % Row 4
    smt_parse('(assert (= (board 4 4) V4))',C9),
    smt_parse('(assert (= (board 4 5) V5))',C10),
    smt_parse('(assert (= (board 4 6) V7))',C11),
    % Row 5
    smt_parse('(assert (= (board 5 3) V1))',C12),
    smt_parse('(assert (= (board 5 7) V3))',C13),
    % Row 6
    smt_parse('(assert (= (board 6 2) V1))',C14),
    smt_parse('(assert (= (board 6 7) V6))',C15),
    smt_parse('(assert (= (board 6 8) V8))',C16),
    % Row 7
    smt_parse('(assert (= (board 7 2) V8))',C17),
    smt_parse('(assert (= (board 7 3) V5))',C18),
    smt_parse('(assert (= (board 7 7) V1))',C19),
    % Row 8
    smt_parse('(assert (= (board 8 1) V9))',C20),
    smt_parse('(assert (= (board 8 6) V4))',C21),

    HardestSudoku = [list(SudokuScript), C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20, C21],
    smt_load_file('sudoku_show_values.smt2',HardestSudoku, Script),
    smt_solve_z3(Script,_).
% 339,657 inferences, 0.041 CPU in 1.208 seconds (3% CPU, 8340463 Lips)
