(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ABV)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 2) Bool))
(declare-fun b () (Array (_ BitVec 2) Bool))
; Both index and element sort are finite, so weakeq-ext creates the term (select a (@diff a a)) itself and with it
; the diff axiom for a Boolean element sort.
(assert (not (= a b)))
(check-sat)
(exit)
