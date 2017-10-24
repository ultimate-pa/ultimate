(set-info :status sat)

(set-logic HORN)

(declare-fun I (Int Int) Bool)

;(assert false)
(assert (forall ((x Int)) (=> (= x 0) (I x 0))))
(assert (forall ((x Int) (x1 Int) (x2 Int)) (=> (and (I x x2) (= x1 (+ x 1))) (I x1 x2))))
(assert (forall ((x Int)) (=> (and (I x 0) (= x (- 1))) false)))


(check-sat)
;(get-model)
