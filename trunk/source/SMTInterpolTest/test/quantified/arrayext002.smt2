(set-option :produce-proofs true)
(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :status unsat)


(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-fun f (Int) Int)
(declare-const i Int)

(assert (forall ((x Int))
   (= (select a x) (f x))))
(assert (forall ((x Int))
   (= (select b x) (f x))))
(assert (not (= a (store b i (f i)))))
(check-sat)
(get-proof)
