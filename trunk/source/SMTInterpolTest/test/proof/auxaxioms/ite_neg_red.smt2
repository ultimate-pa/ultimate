(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c1 () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not q))
(assert p)
(push 1)
(assert (or q (and p (not (ite c1 a b)))))
(assert a)
(assert b)
;(@tautology (! (or (ite c1 a b) (not a) (not b)) :ite+red))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
