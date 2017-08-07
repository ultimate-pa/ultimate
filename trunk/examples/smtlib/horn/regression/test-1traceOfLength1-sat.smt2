; status: sat (checked by z3)
; written on 27.03.2017
; for SSA construction debugging -- has only one trace of length 1
(set-info :status sat)
(set-logic HORN)

(declare-fun I0_x (Int) Bool)
(declare-fun I1_x (Int) Bool)
(declare-fun I2_x (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I0_x x))))
(assert (forall ((x Int)) (=> (and (I0_x x) (< x 0)) false)))
(check-sat)
