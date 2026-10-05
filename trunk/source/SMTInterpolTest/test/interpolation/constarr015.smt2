(set-option :produce-proofs true)
(set-option :produce-interpolants true)
(set-option :proof-check-mode true)
(set-option :interpolant-check-mode true)

(set-logic QF_ALIA)
(set-info :status unsat)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun u () Int)
(declare-fun v () Int)

;; weakeq-ext with a trivial select/const edge: the value of the const array c is the
;; select (select b j), which at the same time is the select that b's weak-j class holds.
;; The lemma therefore contains no equality literal for the select edge; the step is
;; justified by the const axiom alone.
;;
;; Two things are needed to get there.  The store at the weak path index j must be on the
;; const side (b = store c j v), so that the other side's mSelects[j] is the const's own
;; select, and the const term must be created after the store axiom's select
;; (select (store c j v) j), which occupies the same mSelects slot and would otherwise win
;; it -- hence the const equality is asserted last.  u = v forces a = b and thus the lemma.
(assert (! (and (= b (store c j v)) (= a (store c k u)) (not (= k j)) (= u v)) :named A))
(assert (! (and (not (= a b)) (= c ((as const (Array Int Int)) (select b j)))) :named B))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
