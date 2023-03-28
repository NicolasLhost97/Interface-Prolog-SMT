; SMT-LIB2
(set-logic AUFLIA)

(declare-const a (Array Int Int))

; Initialisation du tableau a avec 10 valeurs
(assert (= (select a 0) 3))
(assert (= (select a 1) 7))
(assert (= (select a 2) 9))
(assert (= (select a 3) 15))
(assert (= (select a 4) 18))
(assert (= (select a 5) 22))
(assert (= (select a 6) 25))
(assert (= (select a 7) 29))
(assert (= (select a 8) 32))
(assert (= (select a 9) 35))

(declare-const n Int)
; Taille du tableau : n = 10
(assert (= n 10))

; Vérification de la propriété: a[i] <= a[i+1] pour 0 <= i < n-1
(define-fun is_sorted () Bool
  (forall ((i Int))
    (=> (and (>= i 0) (< i (- n 1)))
        (<= (select a i) (select a (+ i 1))))))

; On cherche à savoir si le tableau est trié
(assert is_sorted)
(check-sat)
