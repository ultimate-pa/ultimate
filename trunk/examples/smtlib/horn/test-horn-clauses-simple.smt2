(set-info :status sat)

(set-logic HORN)

(declare-fun I (Int) Bool)

;(assert false)
(assert (forall ((x Int)) (=> (= x 0) (I x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (I x) (= x1 (+ x 1))) (I x1))))
(assert (forall ((x Int)) (=> (and (I x) (= x (- 1))) false)))
(assert (forall ((x Int) (x1 Int)) (=> (I x) (=> (= x1 (+ x 1)) (I x1)))))
(assert (forall ((x Int) (x1 Int)) (=> (= x1 (+ x 1)) (or (not (I x)) (I x1)))))
(assert (forall ((x Int) (x1 Int)) (or (I x1) (not (I x)) (not (= x1 (+ x 1))))))
(assert (not (exists ((x Int)) (and (I x) (= x (- 1))))))


(check-sat)
;(get-model)
