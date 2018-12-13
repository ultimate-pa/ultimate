; Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
; Date: 2018-12-12
;
; MoNatDiff formulas without universally quantified set variables
; can be encoded as UFLIA. We use this script to check if SMT solvers
; can solve very simple MoNatDiff formulas.
;
; Today, (2018-12-12) recent versions of Z3 and CVC4 returned 'unknown'
; after a few seconds.

(set-logic UFLIA)

(declare-fun I (Int) Bool)

(assert (I 0))
(assert (not (I 1)))
(assert (forall ((y Int)) (=> (and (not (I y)) (<= y 20)) (not (I (+ y 2))))))

(check-sat)
(get-model)
(get-value (I))
