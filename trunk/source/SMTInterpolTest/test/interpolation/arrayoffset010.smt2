(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_ALIA)
(set-info :status unsat)
(declare-const s (Array Int Int))
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const w Int)
(declare-const v Int)
;; weakeq-ext where one side of the select edge is the value of a const array and
;; carries an offset: the edge is { (select a i), v+1 }.  Both ends are fixed shared
;; terms, so linear arithmetic propagates the mixed offset equality
;; (select a i) = v + 1 between the A-local select and the B-local v.  The mixed
;; variable stands for the value at literal level, so the const boundary term must be
;; built from the shifted mixed variable, i.e. (const (+ mixedVar 1)); using the bare
;; mixed variable yields an interpolant that is off by the offset.
(assert (! (and (= a (store s i w)) (= (select a i) 5) (not (= a s))) :named A))
(assert (! (and (= s ((as const (Array Int Int)) (+ v 1))) (= v 4)) :named B))
(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
