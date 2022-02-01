; status: sat (checked by z3)
; written on 27.03.2017
; for SSA construction debugging -- has only one trace of length 4
(set-info :status sat)

(set-logic HORN)

(declare-fun I0_x (Int) Bool)
(declare-fun I1_x (Int) Bool)
(declare-fun I2_x (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I0_x x))))
(assert (forall ((x Int)) (=> (and (I0_x x) (< x 0)) false)))
;(assert (forall ((x Int) (x1 Int)) (=> (and (I0_x x) (= x1 (+ x 1))) (I1_x x1))))
;(assert (forall ((x Int) (x1 Int)) (=> (and (I1_x x) (= x1 (+ x 1))) (I2_x x1))))
;(assert (forall ((x Int)) (=> (and (I2_x x) (< x 0)) false)))

(check-sat)
