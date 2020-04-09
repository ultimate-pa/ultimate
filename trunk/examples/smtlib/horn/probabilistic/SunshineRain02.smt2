; 2020-04-07 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
;
; Set of constraint Horn clauses that represents a Markov chain together with
; a safety property.
;
; The Markov chain has two states s and r (s for sunshine, r for rain), and
; the following transitions:
; (s ---0.25---> r)
; (s ---0.75---> s)
; (r ---0.5----> s)
; (r ---0.5----> r)
; The initial state (state where the system is initially with probability 1) 
; is s.
;
; Our safety property is that the probability of state s is always greater 
; than or equal to three-fifths.

(set-logic HORN)

(declare-fun Is (Real) Bool)
(declare-fun Ir (Real) Bool)
;(define-fun Is ((ps Real)) Bool (>= ps (/ 3.0 5.0)))
;(define-fun Ir ((pr Real)) Bool (< pr (/ 2.0 5.0)))

(assert (forall ((ps Real) (pr Real)) (=> (= ps 1.0) (Is ps))))
(assert (forall ((ps Real) (pr Real)) (=> (= pr 0.0) (Ir pr))))
(assert (forall ((ps Real) (pr Real)) (=> (and (>= ps 0.0) (<= ps 1.0) (>= pr 0.0) (<= pr 1.0) (= (+ ps pr) 1.0) (Is ps) (Ir pr)) (Is (+ (* 0.75 ps) (* 0.5 pr))))))
(assert (forall ((ps Real) (pr Real)) (=> (and (>= ps 0.0) (<= ps 1.0) (>= pr 0.0) (<= pr 1.0) (= (+ ps pr) 1.0) (Is ps) (Ir pr)) (Ir (+ (* 0.25 ps) (* 0.5 pr))))))
(assert (forall ((ps Real) (pr Real)) (=> (and (>= ps 0.0) (<= ps 1.0) (>= pr 0.0) (<= pr 1.0) (= (+ ps pr) 1.0) (Is ps) (< ps (/ 3.0 5.0))) false)))
(check-sat)
(get-model)
