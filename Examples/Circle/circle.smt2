(set-logic QF_NRA)

; Variables
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun x2 () Real)
(declare-fun y2 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun x () Real)
(declare-fun y () Real)

; Valeurs des cercles
(assert (= x1 1))
(assert (= y1 2))
(assert (= x2 4))
(assert (= y2 2))
(assert (= r1 2))
(assert (= r2 1))

; Equations de cercle
(assert (= (* r1 r1) (+ (* (- x x1) (- x x1)) (* (- y y1) (- y y1)))))
(assert (= (* r2 r2) (+ (* (- x x2) (- x x2)) (* (- y y2) (- y y2)))))

; Trouver une solution
(check-sat)
(get-value (x y))
