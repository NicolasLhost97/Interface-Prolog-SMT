(declare-fun x ()
Int )
(declare-fun y ()
Int )
(assert (> x 0 )
)
(assert (> y 0 )
)
(assert (< y 10 )
)
(assert (> y x )
)
(assert (> x 1 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 2 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 3 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 4 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 5 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 6 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 7 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )
(assert (> x 8 )
)
(echo "continue-if-sat")
(check-sat )
(get-model )