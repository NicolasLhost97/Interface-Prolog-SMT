sat
model-to-constraint-start
(x)
(
  (define-fun z () Int
    (- 1))
  (define-fun x () Int
    1)
  (define-fun y () Int
    0)
)
model-to-constraint-end
sat
model-to-constraint-start
(y)
(
  (define-fun x () Int
    0)
  (define-fun z () Int
    (- 2))
  (define-fun y () Int
    (- 1))
  (define-fun x_from_model () Int
    1)
)
model-to-constraint-end
(error "line 27 column 6: named expression already defined")
(error "line 38 column 6: named expression already defined")
(error "line 44 column 0: named expression already defined")
model-to-constraint-start
(y )
(error "line 50 column 12: model is not available")
model-to-constraint-end
sat
model-to-constraint-start
(y)
(
  (define-fun x () Int
    0)
  (define-fun z () Int
    (- 3))
  (define-fun y () Int
    (- 2))
  (define-fun x_from_model () Int
    1)
  (define-fun y_from_model () Int
    (- 1))
)
model-to-constraint-end
model-to-constraint-start
(y )
(
  (define-fun x () Int
    0)
  (define-fun z () Int
    (- 3))
  (define-fun y () Int
    (- 2))
  (define-fun x_from_model () Int
    1)
  (define-fun y_from_model () Int
    (- 1))
)
model-to-constraint-end
model-to-constraint-start
(x )
(
  (define-fun x () Int
    0)
  (define-fun z () Int
    (- 3))
  (define-fun y () Int
    (- 2))
  (define-fun x_from_model () Int
    1)
  (define-fun y_from_model () Int
    (- 1))
)
model-to-constraint-end
