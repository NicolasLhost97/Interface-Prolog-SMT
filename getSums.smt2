(set-option :produce-models true )
(set-logic ALL )
(declare-fun x ()
Int )
(declare-fun y ()
Int )
(assert (>= x 0 )
)
(assert (>= y 0 )
)
(assert (= 2 (+ x y )
)
)
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-1") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-1") ; used to indentify the model converted to constraints
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-2") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-2") ; used to indentify the model converted to constraints
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-3") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-3") ; used to indentify the model converted to constraints
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-4") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-4") ; used to indentify the model converted to constraints
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-5") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-5") ; used to indentify the model converted to constraints
(echo "continue-if-sat")
(check-sat )
(echo "model-to-constraint-start-6") ; used to indentify the model converted to constraints
(echo "(x y)") ; symbols converted to constraints
(get-model )
(echo "model-to-constraint-end-6") ; used to indentify the model converted to constraints
