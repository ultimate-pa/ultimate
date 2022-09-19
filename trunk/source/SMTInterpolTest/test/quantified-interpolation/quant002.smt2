(set-option :print-success false)
;(set-option :produce-proofs true)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-info :source |
   Simple example from Christ and Hoenicke, Instantiation Based Interpolation.
   Example4: A: ALL x. h(x) != a,  B: ALL y. h(g(y)) = y
   We adapted it slightly to fit in our supported fragment.
|)
(set-option :print-terms-cse false)
(set-option :verbosity 5)
(set-logic UF)
(declare-sort U 0)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun a () U)
(declare-fun h (U) U)
(declare-fun g (U) U)
(declare-fun f (U) U)

(assert (! (forall ((x U)) (not (= (h x) (f a)))) :named A))
(assert (! (forall ((y U)) (= (h (g y)) (f y))) :named B))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
