(declare-fun x ()
Int )
(declare-fun y ()
Int )
(declare-fun z ()
Int )
(assert (> x y )
)
(assert (> y z )
)
(check-sat )
(echo "model-to-constraint-start" )
(echo "(x y)" )
(get-model )
(echo "model-to-constraint-end" )
(define-fun x_from_model ()
Int 1 )
(define-fun y_from_model ()
Int 0 )
(assert (not (= x x_from_model )
)
)
(assert (not (= y y_from_model )
)
)
(check-sat )
(echo "model-to-constraint-start" )
(echo "(x y)" )
(get-model )
(echo "model-to-constraint-end" )
