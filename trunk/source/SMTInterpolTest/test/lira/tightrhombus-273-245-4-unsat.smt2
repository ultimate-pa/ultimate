(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_UFLIRA)
(declare-fun x () Int)
(declare-fun y () Real)
(assert (and 
	(<= 0.0 (- (* 27300000.0 (to_real x)) (* 24500001.0 y)))
	(<= (- (* 27300000.0 (to_real x)) (* 24500001.0 y)) 99999.0)
	(<= 1.0 (- (* 27300001.0 (to_real x)) (* 24500000.0 y)))
	(<= (- (* 27300001.0 (to_real x)) (* 24500000.0 y)) 100000.0)))
(assert (<= (- y (to_real (to_int y))) 0.0244901632653061224489))
(check-sat)
(exit)
