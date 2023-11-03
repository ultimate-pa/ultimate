(set-option :print-success false)
;(set-option :produce-proofs true)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-info :source |
   Simple example from Henkel, Hoenicke, Schindler,
   Proof Tree Preserving Sequence Interpolation of
   Quantified Formulas in the Theory of Equality
   Adapted to fall into the supported fragment.
   Example: P1: ALL x. g(h(x)) = x, P2: ALL y. f(g(y)) != b, P3: ALL z. f(z)=z
|)
(set-option :print-terms-cse false)
(set-option :verbosity 5)
(set-logic UF)
(declare-sort U 0)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun b () U)
(declare-fun h (U) U)
(declare-fun g (U) U)
(declare-fun f (U) U)
(declare-fun q (U) U)

(assert (! (forall ((x U)) (= (g (h (q x))) (q x))) :named P1))
(assert (! (forall ((y U)) (not (= (f (g y)) (q b)))) :named P2))
(assert (! (forall ((z U)) (= (f (q z)) (q z))) :named P3))

(check-sat)
(get-interpolants P1 P2 P3)
(get-interpolants P1 P3 P2)
(get-interpolants P2 P1 P3)
(get-interpolants P2 P3 P1)
(get-interpolants P3 P1 P2)
(get-interpolants P3 P2 P1)
(exit)
