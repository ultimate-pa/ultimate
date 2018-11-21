(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

; (assert (exists ((x Int)) (and (< (- y x) 0) (< (- x z) 0))))

(assert (or (= x 0) (= x 1)))

(check-sat)
(get-model)
