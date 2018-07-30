; example script to test if all atomic formulas of MoNatDiff
; are identified correctly

(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInts 0)
(declare-fun element (Int SetOfInts) Bool)
(declare-fun subsetInts (SetOfInts SetOfInts) Bool)
(declare-fun strictSubsetInts (SetOfInts SetOfInts) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun S () SetOfInts)
(declare-fun T () SetOfInts)

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
; X subsetInts Y
(assert (subsetInts S T ))
; X strictSubsetInts Y
(assert (strictSubsetInts T S))

(check-sat)
(get-model)

