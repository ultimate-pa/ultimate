(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_AX)
(declare-sort U 0)
(declare-fun a () (Array U U))
(declare-fun b () (Array U U))
(assert (not (= a b)))
(assert (! (= (select a (@diff a b)) (select b (@diff a b))) :named x))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
