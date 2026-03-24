(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (not (= (bvsub a b) (bvneg (bvsub b a)))))
(check-sat)
(get-proof)
