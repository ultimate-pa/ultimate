(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_LIA)
(declare-fun x () Int)
(assert (>= (mod x 5) 5))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
