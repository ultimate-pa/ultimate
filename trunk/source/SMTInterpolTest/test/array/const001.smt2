(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(assert (= ((as const (Array Int U)) v1) ((as const (Array Int U)) v2)))
(assert (not (= v1 v2)))
(check-sat)
(get-proof)
(exit)

