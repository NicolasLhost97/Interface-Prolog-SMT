sat
model-to-constraint-start
(x y)
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
(x y)
(
  (define-fun x () Int
    0)
  (define-fun z () Int
    (- 2))
  (define-fun y () Int
    (- 1))
  (define-fun x_from_model () Int
    1)
  (define-fun y_from_model () Int
    0)
)
model-to-constraint-end
