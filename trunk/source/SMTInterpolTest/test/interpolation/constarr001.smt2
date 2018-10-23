(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :interpolant-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_AUFLIA)
(declare-fun v () Int)
(declare-fun w () Int)
(declare-fun i () Int)
(declare-fun k () Int)
(declare-fun a () (Array Int Int))

(assert (! (and (not (= v (select a i))) (= a (store ((as const (Array Int Int)) v) k w))) :named A))
(assert (! (not (= i k)) :named B))

(check-sat)
(get-proof)
(get-interpolants A B)
(exit)
