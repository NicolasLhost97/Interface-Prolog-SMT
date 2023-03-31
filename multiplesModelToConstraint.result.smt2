sat
model-to-constraint-start-1
(x y)
(
  (define-fun z () Int
    (- 1))
  (define-fun x () Int
    1)
  (define-fun y () Int
    0)
)
model-to-constraint-end-1
model-to-constraint-start-2
(z)
(
  (define-fun z () Int
    (- 1))
  (define-fun x () Int
    1)
  (define-fun y () Int
    0)
)
model-to-constraint-end-2
sat
model-to-constraint-start-3
(x y z)
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
  (define-fun z_from_model_2 () Int
    (- 1))
)
model-to-constraint-end-3
sat
model-to-constraint-start-4
(x y)
(
  (define-fun x () Int
    (- 1))
  (define-fun z () Int
    (- 3))
  (define-fun y () Int
    (- 2))
  (define-fun z_from_model_3 () Int
    (- 2))
  (define-fun x_from_model_3 () Int
    0)
  (define-fun y_from_model_3 () Int
    (- 1))
  (define-fun y_from_model_1 () Int
    0)
  (define-fun x_from_model_1 () Int
    1)
  (define-fun z_from_model_2 () Int
    (- 1))
)
model-to-constraint-end-4
model-to-constraint-start-5
(x z)
(
  (define-fun x () Int
    (- 1))
  (define-fun z () Int
    (- 3))
  (define-fun y () Int
    (- 2))
  (define-fun z_from_model_3 () Int
    (- 2))
  (define-fun x_from_model_3 () Int
    0)
  (define-fun y_from_model_3 () Int
    (- 1))
  (define-fun y_from_model_1 () Int
    0)
  (define-fun x_from_model_1 () Int
    1)
  (define-fun z_from_model_2 () Int
    (- 1))
)
model-to-constraint-end-5
