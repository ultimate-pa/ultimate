(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))

(push 1)
(assert (not (= ((_ zero_extend 4) (_ bv3 4)) (_ bv3 8))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= ((_ zero_extend 4) (bvsub (_ bv0 4) (_ bv1 4))) (_ bv15 8))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= ((_ zero_extend 4) (bvmul (_ bv7 4) (_ bv12 4))) (_ bv4 8))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= ((_ zero_extend 4) x) (concat (_ bv0 4) x))))
(check-sat)
(pop 1)
