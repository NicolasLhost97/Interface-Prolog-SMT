; Variables et ensemble d'entiers
(declare-const x1 Bool)
(declare-const x2 Bool)
(declare-const x3 Bool)
(declare-const x4 Bool)
(declare-const x5 Bool)
(declare-const x6 Bool)
(declare-const x7 Bool)
(declare-const x8 Bool)
(declare-const x9 Bool)
(declare-const x10 Bool)
(declare-const x11 Bool)
(declare-const x12 Bool)
(declare-const x13 Bool)
(declare-const x14 Bool)
(declare-const x15 Bool)
(declare-const x16 Bool)

; Valeurs des entiers
(define-const v1 Int 3)
(define-const v2 Int 4)
(define-const v3 Int 5)
(define-const v4 Int 6)
(define-const v5 Int 7)
(define-const v6 Int 8)
(define-const v7 Int 9)
(define-const v8 Int 10)
(define-const v9 Int 11)
(define-const v10 Int 13)
(define-const v11 Int 16)
(define-const v12 Int 20)
(define-const v13 Int 24)
(define-const v14 Int 30)
(define-const v15 Int 32)
(define-const v16 Int 40)

; Valeur cible
(define-const target Int 53)

; Contraintes arithmétiques et booléennes
(assert (= target
           (+ (* (ite x1 1 0) v1)
              (* (ite x2 1 0) v2)
              (* (ite x3 1 0) v3)
              (* (ite x4 1 0) v4)
              (* (ite x5 1 0) v5)
              (* (ite x6 1 0) v6)
              (* (ite x7 1 0) v7)
              (* (ite x8 1 0) v8)
              (* (ite x9 1 0) v9)
              (* (ite x10 1 0) v10)
              (* (ite x11 1 0) v11)
              (* (ite x12 1 0) v12)
              (* (ite x13 1 0) v13)
              (* (ite x14 1 0) v14)
              (* (ite x15 1 0) v15)
              (* (ite x16 1 0) v16)
              )))

; Trouver une solution
(check-sat)
(get-model)