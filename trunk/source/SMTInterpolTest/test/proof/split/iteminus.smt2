(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

(push 1)
(assert (not (ite p q r)))
(assert p)
(assert q)

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
(pop 1)

(push 1)
(assert (not (ite p q r)))
(assert (not p))
(assert r)

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
(pop 1)
