; example script to test if all atomic formulas of MoNatDiff
; are identified correctly

(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun S () SetOfInt)
(declare-fun T () SetOfInt)

; assert statements for all atomic formulas of type inequality
; x-y <= c
(assert (<= (- x y) 2))
; x-y < c
(assert (< (- x y) 5))
; x <= c
(assert (<= x 10))
; x < c
(assert (< x 0))
; -x <= c
(assert (<= (- x) 4))
; -x < c
(assert (< (-x) 6))

; assert ststements for all atomic formulas of type element
; x+c element Y
(assert (element (+ x 7) S))
; x element Y (not yet implemented)
; (assert (element x S))
; c element X
(assert (element 8 T))

; assert statements for all atomic formulas of type subset
; X subsetInt Y
(assert (subsetInt S T))

; X strictSubsetInt Y
(assert (strictSubsetInt T S))

(check-sat)
(get-model)

