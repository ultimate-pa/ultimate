(set-option :offset-equalities false)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun v0 () Int)
(declare-fun v2 () Int)
; trivdiseq001 with offset equalities switched off, which is where the two notions
; of "same fact" can drift apart.  The read-over-weakeq lemma needs the trivial
; index disequalities 0 != 1 and 2 != 1.  Without offsets a constant stays part of
; the term, so the proof generator, which keys facts on CCTerms, puts both into the
; clause as two literals; the proof simplifier must key them the same way.  While
; OffsetEqKey split a term into an offset-free part and a constant regardless of the
; option, it saw one fact, resolved both needed disequalities against a single
; literal and built a lemma proving one literal less than its clause.
(assert (= b (store (store a 2 v2) 0 v0)))
(assert (not (= (select b 1) (select a 1))))
(check-sat)
(get-proof)
(exit)
