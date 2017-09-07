(set-info :status unsat)
(set-logic HORN)

(declare-fun Ix1 (Int) Bool)
(declare-fun Ix2 (Int) Bool)
(declare-fun Iy1 (Int) Bool)
(declare-fun Iy2 (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (Ix1 x))))
(assert (forall ((x Int)) (=> (= x 0) (Ix2 x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Ix1 x) (= x1 (+ x 1))) (Ix1 x1))))
(assert (forall ((x Int) (x1 Int)) (=> (and (Ix1 x) (= x1 (+ x 1))) (Ix2 x1))))

(assert (forall ((y Int)) (=> (= y 0) (Iy1 y))))
(assert (forall ((y Int)) (=> (= y 0) (Iy2 y))))
(assert (forall ((y Int) (y1 Int)) (=> (and (Iy1 y) (= y1 (+ y 1))) (Iy1 y1))))
(assert (forall ((y Int) (y1 Int)) (=> (and (Iy1 y) (= y1 (+ y 1))) (Iy2 y1))))

(assert (forall ((x Int) (y Int)) (=> (and (Ix2 x) (Iy2 y) (= x y)) false)))

(check-sat)
;(get-model)
