(set-logic QF_LIA)

(define-sort int16 () Int) 
(declare-fun x () Int)
(declare-fun y () int16)

(define-fun test () Int y)

(assert (< x y))
(check-sat)
(get-model)
