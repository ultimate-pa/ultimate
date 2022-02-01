(set-info :status sat)
(set-logic HORN)

(declare-fun M (Int Int) Bool)

;(assert false)
(assert (forall ((x Int) (r Int)) (=> (and (> x 100) (= r (- x 10))) (M x r))))
(assert (forall ((x Int) (y Int) (r Int)) (=> (and (forall ((x Int)) (and (M y x) (M x r))) (<= x 100) (= y (+ x 11))) (M x r))))
(assert (forall ((x Int) (r Int)) (=> (and (M x r) (<= x 101) (not (= r 91))) false)))


(check-sat)
;(get-model)
