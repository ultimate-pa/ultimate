(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (= (bvsaddo a b) (= (sbv_to_int (bvadd b a)) (+ (sbv_to_int b) (sbv_to_int a)))))
(check-sat)
