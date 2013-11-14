(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and 
	(<= 0 (- (* 28300 x) (* 24501 y)))
	(<= (- (* 28300 x) (* 24501 y)) 99)
	(<= 1 (- (* 28301 x) (* 24500 y)))
	(<= (- (* 28301 x) (* 24500 y)) 100)))
(check-sat)
(exit)
