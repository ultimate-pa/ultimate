(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

; I contains all even numbers including 0.
;(assert (< x 0))
(assert (not (< x 0)))
;(assert (= x 0) )
;(assert (element x I))
;(assert (forall ((y Int)) (=> (element y I) (element (+ y 2) I))))
;(assert (forall ((z Int)) (=> (element z I) (not (element (+ z 1) I)))))

(check-sat)
(get-value (x))
