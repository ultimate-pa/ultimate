;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)

(set-info :status unsat)

(set-logic QF_UFBV)

(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))

(assert (not (= (f (f b)) (f (f c)))))
(assert (= b (_ bv1 8)))
(assert (= c (bvudiv (bvadd b b) (_ bv2 8))))
(check-sat)

(exit)
