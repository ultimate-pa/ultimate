(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun I () SetOfInt)

; I either contains all even numbers or all odd numbers.
(assert (or (= x 0) (= x 1)))
(assert (element x I))
(assert (forall ((x Int)) (=> (element x I) (element (+ x 2) I))))
(assert (forall ((y Int)) (=> (element y I) (not (element (+ y 1) I)))))

(check-sat)
(get-value (x I))
