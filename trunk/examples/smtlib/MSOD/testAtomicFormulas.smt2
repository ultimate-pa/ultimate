; ==============================================================================
; example script to test all atomic formulas of MoNatDiff
; ==============================================================================

(set-logic UFLIA)

; ==============================================================================
; MoNatDiff specific declarations
; ==============================================================================

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun S () SetOfInt)
(declare-fun T () SetOfInt)

; ==============================================================================
; assert statements for all atomic formulas of type inequality
; ==============================================================================

(assert (not (< x 3)))

(assert (<= (- x y) 2))
(assert (< (- x y) 5))
(assert (<= x 10))
(assert (< x 0))
(assert (<= (- x) 4))
(assert (< (- x) 6))

;(assert (<= (+ x 5) 3))

; ==============================================================================
; assert ststements for all atomic formulas of type element
; ==============================================================================

(assert (element (+ x 7) S))
(assert (element x S))
(assert (element 8 T))

;(assert (element (- x 3) S))

; ==============================================================================
; assert statements for all atomic formulas of type subset
; ==============================================================================

(assert (subsetInt S T))
(assert (strictSubsetInt T S))

(check-sat)
(get-model)

