(set-option :produce-proofs true)
(set-info :smt-lib-version 2.6)
(set-logic AUFLIA)
(set-info :status sat)


(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-fun f (Int) Int)
(declare-const i Int)
(declare-const v Int)

(assert (forall ((x Int))
   (= (select a x) (f x))))
(assert (forall ((x Int))
   (= (select b x) (f x))))
(assert (not (= a (store b i v))))
(check-sat)
