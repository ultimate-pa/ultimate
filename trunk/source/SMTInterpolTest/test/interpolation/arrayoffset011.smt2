(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-const s (Array Int Int))
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const w Int)
(declare-const v Int)
;; Same offsetted select edge as arrayoffset010, but with the two partitions asserted in
;; the other order.  The const value v is then the shared term that linear arithmetic
;; registers first, so it becomes the left-hand side of the propagated offset equality
;; v = (select a i) - 1.  The select edge therefore matches the literal with swapped
;; sides, which exercises the other branch of the literal-to-edge shift computation.
(assert (! (and (= s ((as const (Array Int Int)) (+ v 1))) (= v 4)) :named B))
(assert (! (and (= a (store s i w)) (= (select a i) 5) (not (= a s))) :named A))
(check-sat)
(get-interpolants B A)
(get-interpolants A B)
(exit)
