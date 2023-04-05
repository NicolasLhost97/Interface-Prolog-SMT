; Problème des 6 reines avec un solveur SMT et la logique QF_FD

(set-logic QF_FD) ; Logique Quantifier-Free Finite Domains
(set-info :smt-lib-version 2.6)

; Variables pour représenter les positions des reines (indices de colonne)
(declare-const r0 Int)
(declare-const r1 Int)
(declare-const r2 Int)
(declare-const r3 Int)
(declare-const r4 Int)
(declare-const r5 Int)

; Contraintes pour s'assurer que les indices de colonne sont entre 0 et 5
(assert (and (>= r0 0) (< r0 6)))
(assert (and (>= r1 0) (< r1 6)))
(assert (and (>= r2 0) (< r2 6)))
(assert (and (>= r3 0) (< r3 6)))
(assert (and (>= r4 0) (< r4 6)))
(assert (and (>= r5 0) (< r5 6)))

; Contraintes pour s'assurer que les reines ne sont pas sur la même ligne
(assert (distinct r0 r1 r2 r3 r4 r5))

; Fonction pour vérifier si deux reines se menacent en diagonale
(define-fun diagonal-threat ((x1 Int) (y1 Int) (x2 Int) (y2 Int)) Bool
  (= (abs (- x1 x2)) (abs (- y1 y2))))

; Contraintes pour s'assurer que les reines ne se menacent pas en diagonale
(assert (not (diagonal-threat r0 0 r1 1)))
(assert (not (diagonal-threat r0 0 r2 2)))
(assert (not (diagonal-threat r0 0 r3 3)))
(assert (not (diagonal-threat r0 0 r4 4)))
(assert (not (diagonal-threat r0 0 r5 5)))

(assert (not (diagonal-threat r1 1 r2 2)))
(assert (not (diagonal-threat r1 1 r3 3)))
(assert (not (diagonal-threat r1 1 r4 4)))
(assert (not (diagonal-threat r1 1 r5 5)))

(assert (not (diagonal-threat r2 2 r3 3)))
(assert (not (diagonal-threat r2 2 r4 4)))
(assert (not (diagonal-threat r2 2 r5 5)))

(assert (not (diagonal-threat r3 3 r4 4)))
(assert (not (diagonal-threat r3 3 r5 5)))

(assert (not (diagonal-threat r4 4 r5 5)))

; Rechercher une solution
(check-sat)

; Obtenir la solution
(get-value (r0 r1 r2 r3 r4 r5))
