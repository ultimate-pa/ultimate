; status: sat (checked by z3)
; written on 27.03.2017
(set-info :status sat)

(set-logic HORN)

(declare-fun I_x (Int) Bool)
(declare-fun I_y (Int) Bool)
(declare-fun I_z (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (I_x x))))
(assert (forall ((y Int)) (=> (= y 0) (I_y y))))
(assert (forall ((x Int) (x1 Int)) (=> (and (I_x x) (= x1 (+ x 1))) (I_x x1))))
(assert (forall ((y Int) (y1 Int)) (=> (and (I_y y) (= y1 (+ y 1))) (I_y y1))))

(assert (forall ((x Int) (y Int) (z Int)) (=> (and (I_x x) (I_y y) (= (+ x y) z)) (I_z z))))
(assert (forall ((z Int)) (=> (and (I_z z) (< z 0)) false)))

(check-sat)
