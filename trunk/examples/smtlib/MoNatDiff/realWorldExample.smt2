(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

; forall y: y = 0 ==> y \in I
(assert (forall ((y Int)) (=> (<= y 0) (element y I))))

; forall x, y: (x <= 23 /\ x \in I /\ y = x + 2) ==> (y \in I)
(assert (forall ((x Int) (y Int)) (=> (and (<= x 23) (element x I) (= (- y x) 2)) (element y I))))

; forall x: x \in I ==> x != 7
(assert (forall ((x Int)) (=> (element x I) (or (< x 7) (not (<= x 7))))))

;(assert (= x 5))

(check-sat)
(get-model)
