(set-option :produce-models true )
(declare-fun Q (Int) Int)
(declare-const N Int)

; Définir le nombre de reines
(assert (= N 8))

; Les reines sont sur l'échiquier
(assert (forall ((i Int)) (and (<= 0 (Q i)) (< (Q i) N))))

; Les reines ne se menacent pas horizontalement
(assert (forall ((i Int) (j Int))
   (=> (and (<= 0 i) (< i N) (<= 0 j) (< j N) (not (= i j)))
       (not (= (Q i) (Q j))))))

; Les reines ne se menacent pas diagonalement
(assert (forall ((i Int) (j Int))
   (=> (and (<= 0 i) (< i N) (<= 0 j) (< j N) (not (= i j)))
       (not (= (abs (- (Q i) (Q j))) (abs (- i j)))))))

(check-sat)
(get-model)