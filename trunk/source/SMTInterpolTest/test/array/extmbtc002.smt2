(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun u () Int)
(declare-fun w () Int)
(declare-fun y () Int)
; Same as extmbtc001, but the value the store has to differ from is the value of a const array,
; which is not a select term.  Model-based theory combination must compare the const value u with
; the stored value w; since y is pinned to 0, w is pinned to u = 0 and the arrays are equal.
(assert (= a ((as const (Array Int Int)) u)))
(assert (= b (store a i w)))
(assert (not (= a b)))
(assert (= u 0))
(assert (= (+ w y) 0))
(assert (<= y 0))
(assert (<= 0 y))
(check-sat)
(get-proof)
(exit)
