(define-fun N ()
Int 8 )
(declare-fun cols (Int )
Int )
(assert (forall ((i Int )
(j Int )
)
(=> (and (>= i 0 )
(< i N )
(>= j 0 )
(< j N )
(distinct i j )
)
(and (distinct (cols i )
(cols j )
)
(>= (cols i )
0 )
(< (cols i )
N )
(>= (cols j )
0 )
(< (cols j )
N )
)
)
)
)
(assert (forall ((i Int )
(j Int )
)
(=> (and (>= i 0 )
(< i N )
(>= j 0 )
(< j N )
(distinct i j )
)
(distinct (abs (- (cols i )
(cols j )
)
)
(abs (- i j )
)
)
)
)
)
(check-sat )
(get-model )