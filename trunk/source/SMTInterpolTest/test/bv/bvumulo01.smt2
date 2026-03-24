(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (= (bvumulo a b) (= (ubv_to_int (bvmul b a)) (* (ubv_to_int b) (ubv_to_int a)))))
(assert (>= (* (ubv_to_int b) (ubv_to_int a)) 0))
(check-sat)
