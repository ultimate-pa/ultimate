(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

;forall x: x \in I ==> x != 7
;(assert (forall ((x Int)) (=> (element (+ x 0) I) (or (< x 7) (not (<= x 7))))))

;forall x, y: (x <= 1 /\ x \in I /\ y = x + 2) ==> (y \in I)
;(assert (forall ((x Int) (y Int)) (=> (and (<= x 1) (element (+ x 0) I) (= (- y x) 2)) (element y I)))) 

; x >= 2 /\ y < 2 /\ x \in I /\ y \in I
;(assert (and (not (< x 2)) (< y 2) (element x I) (element y I)))


; I is the empty set. 
;(assert (forall ((x Int))  (not (element x I))))

; I is the set of Int/Nat numbers. 
(assert (forall ((x Int))  (element x I)))

;(assert (= x 0))
;(assert (not (element 0 I)))
;(assert (=> (element x I) (element (+ x 1) I)))

(check-sat)

(get-value (I))
