;; Run with: z3 sudoku.smt2

;; This file is structured as follows:
;; 1. Sets up the data types and helper functions.
;; 2. Assertions are made to define what a valid Sudoku solution is.
;; 3. An example board is given, though only some numbers are filled in!
;; 4. This leaves the SMT solver Z3 with the task of filling in the blanks.
;;    This is done with (check-sat), and then the board content is printed.

;; Technically this should be here for the use of (get-value) at the end.x

;; Declare a finite-domain type called Val with 9 possible values V1..V9.
(declare-datatype Val ( (V1) (V2) (V3) (V4) (V5) (V6) (V7) (V8) (V9)))

;; Uninterpreted function that serves as a Sudoku board
;; from (board 0 0) to (board 8 8) because 0-indexing is best indexing.
(declare-fun board (Int Int) Val)

;; Check that an index is in bounds.
(define-fun valid_index ((i Int)) Bool
  (and (>= i 0) (< i 9)))

;; If you use Int instead of Val for values on the board,
;; then uncomment this assertion to ensure that:
;; All values are between 1 and 9 (inclusive).
;(assert
;  (forall ((row Int) (col Int))
;    (and (>= (board row col) 1)
;         (<= (board row col) 9))))

;; All values in a row are unique.
(assert
  (forall ((row Int) (i Int) (j Int))
    (=>
      (and
        (not (= i j))
        (valid_index row)
        (valid_index i)
        (valid_index j))
      (not (= (board row i)
              (board row j))))))

;; All values in a column are unique.
(assert
  (forall ((col Int) (i Int) (j Int))
    (=>
      (and
        (not (= i j))
        (valid_index col)
        (valid_index i)
        (valid_index j))
      (not (= (board i col)
              (board j col))))))

;; All values in each box are unique.
(assert
  (forall ((row1 Int) (col1 Int)
           (row2 Int) (col2 Int))
    (=>
      ;; If the below 3 are true...
      (and
        ;; 1. Row and column indices are in bounds.
        (valid_index row1) (valid_index col1)
        (valid_index row2) (valid_index col2)
        ;; 2. They are not the same elements.
        (or (not (= row1 row2))
            (not (= col1 col2)))
        ;; 3. They do exist in the same box.
        (= (div row1 3) (div row2 3))
        (= (div col1 3) (div col2 3)))
      ;; ... then the values must differ!
      (not (= (board row1 col1)
              (board row2 col2))))))
