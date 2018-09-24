(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_AX)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(define-fun constU ((v U)) (Array U U) ((as const (Array U U)) v))

(assert (= ((as const (Array U U)) v1) ((as const (Array U U)) v2)))
(assert (not (= v1 v2)))
(check-sat)
(get-proof)
(exit)

