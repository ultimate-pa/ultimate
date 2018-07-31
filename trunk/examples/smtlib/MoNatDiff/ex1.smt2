(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (exists ((y Int)) (and (<= (- x y) 2) (<= y 2))))

(check-sat)
(get-model)
