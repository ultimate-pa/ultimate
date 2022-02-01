(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

(assert (or (not (or p q)) r))
(assert p)
(assert (not r))
;(@tautology (! (or (! (or p q) :quoted) (not p)) :or-))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)
