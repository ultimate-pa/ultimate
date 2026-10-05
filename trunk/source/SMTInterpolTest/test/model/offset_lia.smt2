; Model construction with a congruence offset equality: f(y+5) shares the
; offset-free CCTerm y plus a +5 offset, and y is fixed to 3 in arithmetic.
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-info :status sat)
(set-logic QF_UFLIA)
(declare-fun y () Int)
(declare-fun f (Int) Int)
(assert (= (f (+ y 5)) 0))
(assert (= y 3))
(check-sat)
(get-model)
