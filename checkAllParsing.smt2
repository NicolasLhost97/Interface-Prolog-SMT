(set-info :status unknown )
(set-option :interactive-mode true )
(set-option :produce-proofs true )
(set-option :produce-unsat-cores true )
(set-option :produce-unsat-assumptions true )
(set-option :print-success true )
(declare-sort S 0 )
(declare-const a S )
(declare-const x Int )
(declare-datatype DT ((cons (hd S )
(tl DT )
)
(nil )
)
)
(declare-datatypes ((list 0 )
)
(((cons (head Int )
(tail list )
)
(nil )
)
)
)
(set-logic QF_LIA )
(define-sort MyInt ()
Int )
(define-fun f ((x Int )
(y Int )
)
Int (+ x y )
)
(assert (< (f x 2 )
5 )
)
(check-sat )
(get-model )
(get-assertions )
(get-proof )
(get-unsat-core )
(get-assignment )
(get-unsat-assumptions )
(get-value ((f 1 2 )
a )
)
(get-option :print-success )
(get-info :status )
(push 1 )
(pop 1 )
(echo "Hello, world!" )
(reset-assertions )
(exit )