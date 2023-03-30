sat
"model-to-constraint-start-1"
"(x y)"
(model
(define-fun x () Int 1)
(define-fun y () Int 0)
(define-fun z () Int (- 1))
)
"model-to-constraint-end-1"
"model-to-constraint-start-2"
"(z)"
(model
(define-fun x () Int 1)
(define-fun y () Int 0)
(define-fun z () Int (- 1))
)
"model-to-constraint-end-2"
sat
"model-to-constraint-start-3"
"(x y z)"
(model
(define-fun x () Int 0)
(define-fun y () Int (- 1))
(define-fun z () Int (- 2))
)
"model-to-constraint-end-3"
sat
"model-to-constraint-start-4"
"(x y)"
(model
(define-fun x () Int (- 1))
(define-fun y () Int (- 2))
(define-fun z () Int (- 3))
)
"model-to-constraint-end-4"
"model-to-constraint-start-5"
"(x z)"
(model
(define-fun x () Int (- 1))
(define-fun y () Int (- 2))
(define-fun z () Int (- 3))
)
"model-to-constraint-end-5"
