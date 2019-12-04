(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)


(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun I () SetOfInt)
(declare-fun J () SetOfInt)

; I is the set of Int resp. Nat numbers
; 337 states
;(assert (exists ((I SetOfInt)) (forall ((x Int)) (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J)) ))))

; 341 states
(assert (forall ((x Int)) (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J)) )))

; 8 states / 79 states
;(assert (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J))))

; 6 states / 60 states
;(assert (and (element y I) (= x y) (subsetInt I J)))

(check-sat)
