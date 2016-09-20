(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UFLIRA)
(declare-fun x () Real)
(assert (>= (- x (to_int x)) 1.0))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)


