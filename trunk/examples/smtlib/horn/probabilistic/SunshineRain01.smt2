(set-logic HORN)

(declare-fun I0 (Real) Bool)
(declare-fun I1 (Real) Bool)
;(define-fun I0 ((p0 Real)) Bool (and (>= p0 0.5) (<= p0 1.0)))
;(define-fun I1 ((p1 Real)) Bool (and (< p1 0.5) (<= 0.0 p1)))

(assert (forall ((p0 Real) (p1 Real)) (=> (= p0 1.0) (I0 p0))))
(assert (forall ((p0 Real) (p1 Real)) (=> (= p1 0.0) (I1 p1))))
(assert (forall ((p0 Real) (p1 Real)) (=> (and (>= p0 0.0) (<= p0 1.0) (>= p1 0.0) (<= p1 1.0) (= (+ p0 p1) 1.0) (I0 p0) (I1 p1)) (I1 (+ (* (/ 1.0 3.0) p0) (* (/ 2.0 3.0) p1))))))
(assert (forall ((p0 Real) (p1 Real)) (=> (and (>= p0 0.0) (<= p0 1.0) (>= p1 0.0) (<= p1 1.0) (= (+ p0 p1) 1.0) (I0 p0) (I1 p1)) (I0 (+ (* (/ 2.0 3.0) p0) (* (/ 1.0 3.0) p1))))))
(assert (forall ((p0 Real) (p1 Real)) (=> (and (= (+ p0 p1) 1.0) (I1 p1) (>= p1 0.5)) false)))

(check-sat)
(get-model)
