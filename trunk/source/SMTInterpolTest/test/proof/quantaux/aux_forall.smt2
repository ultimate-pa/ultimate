(set-option :produce-proofs true)
(set-logic UF)

(declare-sort U 0)
(declare-fun f (Bool) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U U) Bool)

(assert (not (p a b)))
(assert (p b a))
(assert (forall ((x U)) (= (f (forall ((y U)) (= (f (p y x)) a))) a)))

(assert (= (f false) b))
(check-sat)
(get-proof)
