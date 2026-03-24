(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (not (= (bvnot a) (bvsub ((_ int_to_bv 32) (- 1)) a))))
(check-sat)
(get-proof)
