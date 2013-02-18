(set-option :produce-proofs true)
(set-logic QF_UF)
(set-info :source |
Wikipedia example for Craig interpolation from April 2011.
This is a purely propositional example.

Converted to smtlib by Jochen Hoenicke.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun t () Bool)
(assert (! (=> (not (and p q)) (and (not r) q)) :named a))
(assert (! (not (or (=> t p) (=> t (not r)))) :named b))
(check-sat)
(get-interpolants a b)
(exit)
