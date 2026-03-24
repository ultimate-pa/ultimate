(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (= (bvssubo a b) (= (sbv_to_int (bvsub a b)) (- (sbv_to_int a) (sbv_to_int b)))))
(check-sat)
