; Déclaration de la logique et des constantes
(set-logic QF_LIA)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const d3 Int)
(declare-const s1 Int)
(declare-const s2 Int)
(declare-const s3 Int)
(declare-const e1 Int)
(declare-const e2 Int)
(declare-const e3 Int)

; Attribution des durées des tâches
(assert (= d1 3))
(assert (= d2 4))
(assert (= d3 2))

; Contraintes sur les dates de début et de fin des tâches
(assert (= e1 (+ s1 d1)))
(assert (= e2 (+ s2 d2)))
(assert (= e3 (+ s3 d3)))

; Les dates de début des tâches sont non négatives
(assert (>= s1 0))
(assert (>= s2 0))
(assert (>= s3 0))

; Les tâches ne se chevauchent pas
(assert (or (<= e1 s2) (<= e2 s1)))
(assert (or (<= e1 s3) (<= e3 s1)))
(assert (or (<= e2 s3) (<= e3 s2)))

; Déclaration d'une variable pour la durée totale
(declare-const total_duration Int)

; Contrainte pour minimiser la durée totale
(assert (= total_duration (ite (< e1 e2) e2 e1)))
(assert (<= e3 total_duration))

; Objectif : minimiser la durée totale
(minimize total_duration)

; Vérification et solution
(check-sat)
(get-model)
