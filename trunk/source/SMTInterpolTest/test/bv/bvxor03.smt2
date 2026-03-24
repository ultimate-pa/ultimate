(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))

(assert (= (bvxor a #x0000ffff) #x5678edcb))
(check-sat)
(get-model)

(assert (not (= a #x56781234)))
(check-sat)
(get-proof)
