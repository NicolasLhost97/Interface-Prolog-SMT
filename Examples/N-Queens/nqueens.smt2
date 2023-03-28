(define-fun N () Int 8)

; Déclaration des variables pour chaque reine
(declare-fun cols (Int) Int)

; Les reines sont placées sur différentes colonnes et dans la plage de 0 à N-1
(assert (forall ((i Int) (j Int))
  (=> (and (>= i 0) (< i N) (>= j 0) (< j N) (distinct i j))
      (and (distinct (cols i) (cols j))
           (>= (cols i) 0) (< (cols i) N)
           (>= (cols j) 0) (< (cols j) N)
      )
  )
))

; Les reines ne sont pas sur la même diagonale
(assert (forall ((i Int) (j Int))
  (=> (and (>= i 0) (< i N) (>= j 0) (< j N) (distinct i j))
      (distinct (abs (- (cols i) (cols j))) (abs (- i j)))
  )
))

; Trouver une solution
(check-sat)
(get-model)

; Imprimer les positions des reines
;(echo "Solution (row, col):")
;(get-value ((cols 0)))
;(get-value ((cols 1)))
;(get-value ((cols 2)))
;(get-value ((cols 3)))
;(get-value ((cols 4)))
;(get-value ((cols 5)))
;(get-value ((cols 6)))
;(get-value ((cols 8)))
;(get-value ((cols 9)))
;(get-value ((cols 10)))
;(get-value ((cols 11)))
;(get-value ((cols 12)))
;(get-value ((cols 13)))
;(get-value ((cols 14)))
;(get-value ((cols 15)))
