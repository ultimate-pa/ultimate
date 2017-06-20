(set-logic HORN)

(declare-fun I (Int) (Int) Bool)

;(assert false)
(assert (forall ((x Int)) (=> (= x 0) (and (I x x) (I x 0)))))
(assert (forall ((x Int) (x1 Int)) (=> (and (I x 0) (= x1 (+ x 1))) (and (I x1 x) (I x1 0)))))
(assert (forall ((x Int)) (=> (and (I x 0) (= x (- 1))) false)))


(check-sat)
;(get-model)
