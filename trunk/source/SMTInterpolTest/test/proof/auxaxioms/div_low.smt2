(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UFLIRA)
(declare-fun x () Int)
(assert (< (mod x 5) 0))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
