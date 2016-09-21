(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status sat)
(set-logic QF_LIRA)
(declare-fun x () Int)
(declare-fun y () Real)
(assert (and 
	(<= 0 (- (* 28300000 (to_real x)) (* 24500001 y)))
	(<= (- (* 28300000 (to_real x)) (* 24500001 y)) 99999)
	(<= 1 (- (* 28300001 (to_real x)) (* 24500000 y)))
	(<= (- (* 28300001 (to_real x)) (* 24500000 y)) 100000)))
(assert (<= (- y (to_int y)) 0.0000027755101))
;(assert (<= (- y (to_int y)) (- (/ 68 24500001) (/ 1 1000000000))))
(check-sat)
(exit)
