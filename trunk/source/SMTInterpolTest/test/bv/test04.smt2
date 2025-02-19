;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)

(set-info :status sat)

(set-logic QF_UFBV)

(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const k Int)

(assert (= (f (f b)) (f (f c))))
(assert (= (f b) (_ bv1 8)))
(assert (= (f c) ((_ nat2bv 8) k)))
(assert (distinct (f (f b)) (f b) b c))
(assert (= k 257))
(check-sat)
(get-model)

(exit)
