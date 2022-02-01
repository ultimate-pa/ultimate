(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UFLIRA)
(declare-fun x () Real)
(declare-fun y () Real)

(push 1)
(assert (< x (to_int x)))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (< (- y (to_int x)) (to_int (- y (to_int x)))))
(check-sat)
(get-proof)
(pop 1)


