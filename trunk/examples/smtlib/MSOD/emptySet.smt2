(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

; I is the empty set. Result: sat 
(assert (forall ((x Int))  (not (element x I))))

(check-sat)
(get-value (I))
