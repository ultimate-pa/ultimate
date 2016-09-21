(set-option :produce-proofs true)
(set-option :proof-check-mode true)


(set-logic QF_AX)
(declare-sort U 0)
(declare-fun i () U)
(declare-fun j () U)
(declare-fun a () (Array U Bool))
; this is possibly the only way to trigger this axiom
(assert (select (store a i false) j))
(assert (= i j))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
