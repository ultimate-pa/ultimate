(set-logic QF_BV)

(define-sort bla () (_ BitVec 5))
(declare-fun x () (_ BitVec 5))
(declare-fun y () bla)

(define-fun test () bla y)
;(assert (< x y)
(check-sat)
