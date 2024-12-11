(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const x (_ BitVec 256))
(declare-const y (_ BitVec 256))

(push 1)
(assert (not (= (bvshl x (_ bv0 256)) x)))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvlshr (bvshl x (_ bv172 256)) (_ bv172 256)) x)))
(assert (bvult x (bvshl (_ bv1 256) (_ bv84 256))))
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvlshr (bvshl x y) y) x)))
(assert (bvult y (_ bv255 256)))
(assert (bvult x (bvshl (_ bv1 256) (bvsub (_ bv256 256) y))))
(check-sat)
(pop 1)

