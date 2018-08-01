; ==============================================================================
; Test identification of basic term types
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

(assert x)
(assert S)
(assert (<= x y))

(check-sat)
(get-model)
