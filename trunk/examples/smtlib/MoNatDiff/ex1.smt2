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
(declare-fun J () SetOfInt)

; (assert (exists ((x Int)) (and (< (- y x) 0) (< (- x z) 0))))

(assert (element 5 I))
(assert (element 1 I))
(assert (element 7 I))
(assert (element 3 I))
(assert (element 2 I))
(assert (or (> x 5) (< x 6)))

(check-sat)
(get-value (x J I y))
