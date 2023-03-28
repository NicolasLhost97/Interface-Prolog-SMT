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
model-to-constraint-1
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
  (define-fun y_from_model_1 () Int
    0)
  (define-fun x_from_model_1 () Int
    1)
)
model-to-constraint-end
model-to-constraint-2
