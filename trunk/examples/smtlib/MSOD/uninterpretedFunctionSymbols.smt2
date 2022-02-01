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

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun y () Int)
(declare-fun I () SetOfInt)

; Result: sat
(assert (element 0 I))
(assert (not (element 1 I)))
(assert (forall ((y Int)) (=> (and (not (element y I)) (<= y 20)) (not (element (+ y 2) I)))))

(check-sat)
(get-value (I))
