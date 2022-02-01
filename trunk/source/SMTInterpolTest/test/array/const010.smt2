(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(define-fun constU ((v U)) (Array Int U) ((as const (Array Int U)) v))

(assert (= (constU v1) (constU v2)))
(check-sat)
(get-model)
(get-value ((@diff (constU v1) (constU v2))))
(exit)

