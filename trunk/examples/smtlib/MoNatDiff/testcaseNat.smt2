(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)

; x-y < 5
(assert (< (- x y) 5))

; Model: x=7, y = 3
(assert (= x 7))
(assert (= y 3))

(check-sat)
