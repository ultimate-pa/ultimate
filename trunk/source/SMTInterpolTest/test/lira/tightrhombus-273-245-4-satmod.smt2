(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status sat)
(set-logic QF_UFLIRA)
(declare-fun x () Int)
(declare-fun y () Real)
(declare-fun z () Int)
(assert (and 
	(<= 0.0 (- (* 27300000.0 x) (* 24500001.0 y)))
	(<= (- (* 27300000.0 x) (* 24500001.0 y)) 99999.0)
	(<= 1.0 (- (* 27300001.0 x) (* 24500000.0 y)))
	(<= (- (* 27300001.0 x) (* 24500000.0 y)) 100000.0)))
(assert (< (- y z) 0.0244901632653061224490))
(assert (<= 0 (- y z)))
(check-sat)
(exit)
