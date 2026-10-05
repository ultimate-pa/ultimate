(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_UFDT)
(set-info :status unsat)
(declare-datatypes ((D 0)) (((mk (f Bool)) (nil))))
(declare-fun x () D)
(declare-fun g (Bool) Bool)
; The match axiom equates the match term with the term of the matching case.  The match term is Boolean here, so
; this equality is not a literal and has to be rewritten.
(assert (g (match x (((mk y) y) (nil false)))))
(assert (not (g (f x))))
(assert ((_ is mk) x))
(check-sat)
(get-proof)
(exit)
