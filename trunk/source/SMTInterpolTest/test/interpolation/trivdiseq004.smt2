(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun v0 () Int)
(declare-fun v2 () Int)
; The read-over-weakeq lemma needs the trivial index disequalities 0 != 1 and
; 2 != 1, which express the same affine fact up to a shift and to the sign.
(assert (! (= b (store (store a 2 v2) 0 v0)) :named A))
(assert (! (not (= (select b 1) (select a 1))) :named B))
(check-sat)
(get-proof)
(get-interpolants A B)
