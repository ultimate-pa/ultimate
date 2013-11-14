(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and 
	(<= 0 (- (* 2830 x) (* 2451 y)))
	(<= (- (* 2830 x) (* 2451 y)) 9)
	(<= 1 (- (* 2831 x) (* 2450 y)))
	(<= (- (* 2831 x) (* 2450 y)) 10)))
(check-sat)
(exit)
