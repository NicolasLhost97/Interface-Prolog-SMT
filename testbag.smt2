; Déclaration des constantes pour la taille du plateau et les reines
(define-const N Int 20)

; Déclaration des variables pour les positions des reines
(declare-fun q1 () Int)
(declare-fun q2 () Int)
(declare-fun q3 () Int)
(declare-fun q4 () Int)
(declare-fun q5 () Int)
(declare-fun q6 () Int)
(declare-fun q7 () Int)
(declare-fun q8 () Int)
(declare-fun q9 () Int)
(declare-fun q10 () Int)
(declare-fun q11 () Int)
(declare-fun q12 () Int)
(declare-fun q13 () Int)
(declare-fun q14 () Int)
(declare-fun q15 () Int)
(declare-fun q16 () Int)
(declare-fun q17 () Int)
(declare-fun q18 () Int)
(declare-fun q19 () Int)
(declare-fun q20 () Int)

; Liste des variables pour faciliter l'écriture des contraintes
(define-const queens (Array Int Int) (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (as const (Array Int Int)) q1) 2 q2) 3 q3) 4 q4) 5 q5) 6 q6) 7 q7) 8 q8) 9 q9) 10 q10) 11 q11) 12 q12) 13 q13) 14 q14) 15 q15) 16 q16) 17 q17) 18 q18) 19 q19) 20 q20))

; Contraintes de domaine pour les positions des reines
(assert (and (>= q1 0) (< q1 N)))
(assert (and (>= q2 0) (< q2 N)))
(assert (and (>= q3 0) (< q3 N)))
(assert (and (>= q4 0) (< q4 N)))
(assert (and (>= q5 0) (< q5 N)))
(assert (and (>= q6 0) (< q6 N)))
(assert (and (>= q7 0) (< q7 N)))
(assert (and (>= q8 0) (< q8 N)))
(assert (and (>= q9 0) (< q9 N)))
(assert (and (>= q10 0) (< q10 N)))
(assert (and (>= q11 0) (< q11 N)))
(assert (and (>= q12 0) (< q12 N)))
(assert (and (>= q13 0) (< q13 N)))
(assert (and (>= q14 0) (< q14 N)))
(assert (and (>= q15 0) (< q15 N)))
(assert (and (>= q16 0) (< q16 N)))
(assert (and (>= q17 0) (< q17 N)))
(assert (and (>= q18 0) (< q18 N)))
(assert (and (>= q19 0) (< q19 N)))
(assert (and (>= q20 0) (< q20 N)))

Fonction pour vérifier si deux reines se menacent
(define-fun threaten ((i Int) (j Int)) Bool
  (let ((qi (select queens i)) (qj (select queens j)))
    (or (= qi qj) (= (abs (- qi qj)) (abs (- i j))))
  )
)

; Fonction pour vérifier si une reine est menacée par les autres
(define-fun safe ((i Int)) Bool
  (let ((threats (forall ((j Int)) (=> (and (< j N) (distinct i j)) (not (threaten i j))))))
    (and (>= i 0) (< i N) threats)
  )
)

; Contraintes pour s'assurer que chaque reine est en sécurité
(assert (safe 0))
(assert (safe 1))
(assert (safe 2))
(assert (safe 3))
(assert (safe 4))
(assert (safe 5))
(assert (safe 6))
(assert (safe 7))
(assert (safe 8))
(assert (safe 9))
(assert (safe 10))
(assert (safe 11))
(assert (safe 12))
(assert (safe 13))
(assert (safe 14))
(assert (safe 15))
(assert (safe 16))
(assert (safe 17))
(assert (safe 18))
(assert (safe 19))

; Vérification et solution
(check-sat)
(get-value (queens))

