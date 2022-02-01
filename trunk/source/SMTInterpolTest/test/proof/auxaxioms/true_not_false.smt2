(set-option :produce-proofs true)
(set-option :proof-check-mode true)


(set-logic QF_ALIA)
; using array theory is possibly the only way to trigger this axiom
(push 1)
(assert (= ((as const (Array Int Bool)) true) ((as const (Array Int Bool)) false)))
(check-sat)
(set-option :print-terms-cse false)
(get-proof)
(pop 1)
