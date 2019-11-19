(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun w () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun I () SetOfInt)

; I contains all negative even numbers (excluding 0). Result: sat (IntBuchi), unsat (*Weak, NatBuchi)

; -2 is element of I.
(assert (and (element x I) (= (- x) 2)))

; if y is element of I, then (y-2) is element of I and (y-1) is not element of I.
(assert (forall ((y Int)) (=> (element y I) (and (element z I) (= (- y z) 2) (< y 0) (not (and (element w I) (= (- y w) 1) ))))))


; if y is element of I, it holds that (y-2) is element of I and y is a negative number.
; (assert (forall ((y Int)) (=> (element y I) (and (element z I) (= (- y z) 2) (< y 0)))))


(check-sat)
(get-value (x I))
