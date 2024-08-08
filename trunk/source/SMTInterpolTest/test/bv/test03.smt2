;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)

(set-info :status sat)

(set-logic QF_UFBV)

(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))

(assert (= (f (f b)) (f (f c))))
(assert (= (f b) (_ bv1 8)))
(assert (= (f c) (bvudiv (bvadd (f b) (f b)) (_ bv2 8))))
(check-sat)
(get-model)

(exit)
