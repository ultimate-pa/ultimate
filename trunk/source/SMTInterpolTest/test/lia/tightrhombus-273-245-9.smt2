(set-info :source |A tight rhombus without a feasible integer solution.  This
benchmark is designed to be hard for the algorithm by Dillig, Dillig, and Aiken.
Authors: The SMTInterpol team|)
(set-info :category "crafted")
(set-info :status unsat)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and 
	(<= 0 (- (* 2730000000000 x) (* 2450000000001 y)))
	(<= (- (* 2730000000000 x) (* 2450000000001 y)) 9999999999)
	(<= 1 (- (* 2730000000001 x) (* 2450000000000 y)))
	(<= (- (* 2730000000001 x) (* 2450000000000 y)) 10000000000)))
(check-sat)
(exit)
