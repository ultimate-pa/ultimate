(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UFLIRA)
(declare-fun x () Real)

(push 1)
(assert (>= (- x (to_int x)) 1.0))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (>= (- (* 2 x) (to_int (+ (to_int x) x))) 2.0))
(check-sat)
(get-proof)
(pop 1)

