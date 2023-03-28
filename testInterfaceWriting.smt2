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
(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints
(echo "(x)") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
(define-fun x_from_model ()
Int 1 )
(assert (not (= x x_from_model )
)
)
(check-sat )
(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints
(echo "(y)") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
(define-fun x_from_model ()
Int 1 )
(assert (not (= x x_from_model )
)
)
(def(define-fun x_from_model ()
Int 1 )
(define-fun y_from_model ()
Int 0 )
(assert (not (= x x_from_model )
)
)
(assert (not (= y y_from_model )
)
)
(define-fun x_from_model ()
Int 0 )
(define-fun y_from_model ()
Int (- 1 )
)
(assert (not (= x x_from_model )
)
)
(assert (not (= y y_from_model )
)
)
d to constraints
(echo "(y )") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
(check-sat )
(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints
(echo "(y)") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints
(echo "(y )") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
(echo "model-to-constraint-start") ; used to indentify the model coverted to constraints
(echo "(x )") ; symbols coverted to constraints
(get-model )
(echo "model-to-constraint-end") ; used to indentify the model coverted to constraints
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
(define-fun x_from_model ()
Int 0 )
(define-fun y_from_model ()
Int (- 1 )
)
(assert (not (= x x_from_model )
)
)
(assert (not (= y y_from_model )
)
)
