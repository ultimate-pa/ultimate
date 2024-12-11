;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)

(set-info :status unsat)

(set-logic QF_UFBV)

(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun a () (_ BitVec 8))

(assert (= (f (_ bv0 8)) (_ bv42 8)))
(assert (= a (_ bv1 8)))
(assert (not (= (f (bvadd a (_ bv255 8))) (_ bv42 8))))

(check-sat)

(exit)
