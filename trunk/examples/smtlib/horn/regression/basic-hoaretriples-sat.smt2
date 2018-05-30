(set-logic HORN)
(set-info :status sat)

(declare-fun I (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (I x) (= x1 (+ x 1))) (I x1))))
(assert (forall ((x Int)) (=> (and (I x) (= x (- 1))) false)))


(check-sat)
