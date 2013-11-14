(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and 
	(<= 0 (- (* 28300000 x) (* 24500001 y)))
	(<= (- (* 28300000 x) (* 24500001 y)) 99999)
	(<= 1 (- (* 28300001 x) (* 24500000 y)))
	(<= (- (* 28300001 x) (* 24500000 y)) 100000)))
(check-sat)
(exit)
