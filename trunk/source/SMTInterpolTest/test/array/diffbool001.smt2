(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
; The diff axiom states that a and b differ at (@diff a b) unless they are equal.  Its literal is an equality
; between the two selects, which for a Boolean element sort is not a literal and has to be rewritten.
(assert (not (= a b)))
(assert (= (select a (@diff a b)) (select b (@diff a b))))
(check-sat)
(get-proof)
(exit)
