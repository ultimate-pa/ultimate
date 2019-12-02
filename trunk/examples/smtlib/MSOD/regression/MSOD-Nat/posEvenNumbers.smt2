(set-logic UFLIA)
(set-info :status sat)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)

(declare-fun y () Int)
(declare-fun I () SetOfInt)

; I contains all positive even numbers including 0.
(assert (element 0 I))
(assert (forall ((y Int)) (=> (element y I) (and (element (+ y 2) I) (>= y 0) (not (element (+ y 1) I))))))

(check-sat)