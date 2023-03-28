
; Déclarer le tableau d'entiers initial
(declare-const a (Array Int Int))
(assert (= (select a 0) 4))
(assert (= (select a 1) 1))
(assert (= (select a 2) 3))
(assert (= (select a 3) 2))

; Déclarer le tableau d'entiers trié
(declare-const b (Array Int Int))

; Déclarer les fonctions auxiliaires
(define-fun mini ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun is-sorted ((c (Array Int Int)) (n Int)) Bool
  (forall ((i Int)) (=> (and (>= i 0) (< i (- n 1))) (<= (select c i) (select c (+ i 1))))))
(define-fun is-permutation ((c1 (Array Int Int)) (c2 (Array Int Int)) (n Int)) Bool
  (forall ((i Int)) (=> (and (>= i 0) (< i n))
    (exists ((j Int)) (and (>= j 0) (< j n) (= (select c1 i) (select c2 j)))))))

; Déclarer les contraintes pour vérifier si b est la version triée de a
(assert (is-sorted b 4))
(assert (is-permutation a b 4))

; Vérifier la satisfaisabilité
(check-sat)

; Extraire le tableau trié
(get-value (b))