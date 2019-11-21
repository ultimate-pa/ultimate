(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

(assert (= y (- 3)))
(assert (= z 4))
(assert (element 1 I))
(assert (element (- 2) I))
(assert (element (- 5) I))

(assert (forall ((x Int)) (=> (and (< x 4) (> x 1)) (element x I))))



(check-sat)
(get-value (y z I))