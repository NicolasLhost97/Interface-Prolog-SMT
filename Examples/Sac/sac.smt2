; Déclaration des constantes
(declare-const w1 Int)
(declare-const w2 Int)
(declare-const w3 Int)
(declare-const w4 Int)
(declare-const w5 Int)
(declare-const w6 Int)
(declare-const w7 Int)
(declare-const w8 Int)
(declare-const w9 Int)
(declare-const w10 Int)
(declare-const w11 Int)
(declare-const w12 Int)

(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(declare-const v4 Int)
(declare-const v5 Int)
(declare-const v6 Int)
(declare-const v7 Int)
(declare-const v8 Int)
(declare-const v9 Int)
(declare-const v10 Int)
(declare-const v11 Int)
(declare-const v12 Int)

(declare-const C Int)

; Attribution des poids et valeurs
(assert (= w1 5))
(assert (= w2 3))
(assert (= w3 2))
(assert (= w4 1))
(assert (= w5 4))
(assert (= w6 6))
(assert (= w7 7))
(assert (= w8 15))
(assert (= w9 9))
(assert (= w10 7))
(assert (= w11 3))
(assert (= w12 4))

(assert (= v1 60))
(assert (= v2 50))
(assert (= v3 70))
(assert (= v4 30))
(assert (= v5 50))
(assert (= v6 60))
(assert (= v7 80))
(assert (= v8 200))
(assert (= v9 100))
(assert (= v10 75))
(assert (= v11 65))
(assert (= v12 70))
; Déclaration des variables pour les objets sélectionnés
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)
(declare-const x8 Int)
(declare-const x9 Int)
(declare-const x10 Int)
(declare-const x11 Int)
(declare-const x12 Int)


; Les objets sélectionnés sont soit 0 (non sélectionné) soit 1 (sélectionné)
(assert (and (>= x1 0) (<= x1 1)))
(assert (and (>= x2 0) (<= x2 1)))
(assert (and (>= x3 0) (<= x3 1)))
(assert (and (>= x4 0) (<= x4 1)))
(assert (and (>= x5 0) (<= x5 1)))
(assert (and (>= x6 0) (<= x6 1)))
(assert (and (>= x7 0) (<= x7 1)))
(assert (and (>= x8 0) (<= x8 1)))
(assert (and (>= x9 0) (<= x9 1)))
(assert (and (>= x10 0) (<= x10 1)))
(assert (and (>= x11 0) (<= x11 1)))
(assert (and (>= x12 0) (<= x12 1)))

; Capacité
(assert (= C 15))

; Contrainte de capacité
(assert (<= (+ (* w1 x1) (* w2 x2) (* w3 x3) (* w4 x4) (* w5 x5) (* w6 x6) (* w7 x7) (* w8 x8) (* w9 x9) (* w10 x10) (* w11 x11) (* w12 x12)) C))

; Déclaration d'une variable pour le seuil de valeur
(declare-const threshold Int)

; Contrainte pour vérifier si une solution existe avec une valeur supérieure ou égale au seuil
(assert (>= 
(+ (* v1 x1) (* v2 x2) (* v3 x3) (* v4 x4) (* v5 x5) (* v6 x6) (* v7 x7) (* v8 x8) (* v9 x9) (* v10 x10) (* v11 x11) (* v12 x12)) threshold))

; Définir le seuil de valeur (à ajuster manuellement)
(assert (= threshold 295))

; Vérification et solution
(check-sat)
(get-model)
