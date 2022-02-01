(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_UFLIRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and 
	(<= 0.0 (- (* 27300000.0 x) (* 24500001.0 y)))
	(<= (- (* 27300000.0 x) (* 24500001.0 y)) 99999.0)
	(<= 100000.0 (- (* 27300001.0 x) (* 24500000.0 y)))
	(<= (- (* 27300001.0 x) (* 24500000.0 y)) 199999.0)))
(assert (< (+ (- y (to_real (to_int y))) (- x (to_real (to_int x)))) 0.00193))
(check-sat)
;(get-value ((+ (- y (to_real (to_int y))) (- x (to_real (to_int x))))))
(exit)
