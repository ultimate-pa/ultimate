(set-info :status unsat)
(set-logic HORN)

(declare-fun I (Int) Bool)

;(assert false)
(assert (forall ((x Int)) (=> (= x 0) (I x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (I x) (= x1 (+ x 1))) (I x1))))
(assert (forall ((x Int)) (=> (and (I x) (= x 2)) false)))


(check-sat)
;(get-model)
