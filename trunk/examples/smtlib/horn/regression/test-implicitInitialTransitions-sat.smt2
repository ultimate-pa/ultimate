; status: sat (checked by z3)
; written on 27.03.2017
; currently, we say this set is sat without looking at any trace, because the "initial transitions" 
; don't have the form of an implication withough uninterpreted predicates in the body.
(set-logic HORN)

(declare-fun I_x (Int) Bool)
(declare-fun I_y (Int) Bool)
(declare-fun I_z (Int) Bool)

(assert (I_x 0)) ; equivalent to "(=> (= x 0) (I_x x))", but not translated like that right now..
(assert (I_y 0))
(assert (forall ((x Int) (x1 Int)) (=> (and (I_x x) (= x1 (+ x 1))) (I_x x1))))
(assert (forall ((y Int) (y1 Int)) (=> (and (I_y y) (= y1 (+ y 1))) (I_y y1))))

(assert (forall ((x Int) (y Int) (z Int)) (=> (and (I_x x) (I_y y) (= (+ x y) z)) (I_z z))))
(assert (forall ((z Int)) (=> (and (I_z z) (< z 0)) false)))

(check-sat)
