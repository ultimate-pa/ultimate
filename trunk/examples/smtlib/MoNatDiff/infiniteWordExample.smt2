(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

;(exists x: x \in I) /\ (forall x: x \in I ==> x + 1 \in I)
(assert (exists ((x Int)) (element x I)))
(assert (forall ((x Int)) (=> (element x I) (element (+ x 1) I))))

(check-sat)
