(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun y () Int)
; The disequality a != b holds only if the stored value z differs from a[i].  The array theory
; sees that z and w = a[i] are in different congruence classes and is happy, so the values must
; be kept apart by model-based theory combination.  Since y is pinned to 0, w is pinned to 0 as
; well, i.e. w and z do have the same value and the arrays are equal after all.
(assert (= z 0))
(assert (= b (store a i z)))
(assert (not (= a b)))
(assert (= w (select a i)))
(assert (= (+ w y) 0))
(assert (<= y 0))
(assert (<= 0 y))
(check-sat)
(get-proof)
(exit)
