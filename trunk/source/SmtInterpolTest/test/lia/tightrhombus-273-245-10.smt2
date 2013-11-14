(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and 
	(<= 0 (- (* 27300000000000 x) (* 24500000000001 y)))
	(<= (- (* 27300000000000 x) (* 24500000000001 y)) 99999999999)
	(<= 1 (- (* 27300000000001 x) (* 24500000000000 y)))
	(<= (- (* 27300000000001 x) (* 24500000000000 y)) 100000000000)))
(check-sat)
(exit)
