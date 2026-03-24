(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (= (bvuaddo a b) (= (ubv_to_int (bvadd b a)) (+ (ubv_to_int b) (ubv_to_int a)))))
(check-sat)
