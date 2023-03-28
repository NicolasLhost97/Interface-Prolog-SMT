(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int Int) Int)
(echo "success")
(assert (> (+ x y) 12))
(echo "success")
(check-sat)
(echo "model-to-constrait-start") ; used to indentify the model coverted to constraints
(get-model)
(echo "model-to-constrait-end") ; used to indentify the model coverted to constraints
(echo "success")
(echo "success")
(echo "unsat")
(assert (> x 20))
(check-sat)
(echo "model-to-constrait-start") ; used to indentify the model coverted to constraints
(get-model)
(echo "model-to-constrait-end") ; used to indentify the model coverted to constraints
(exit)