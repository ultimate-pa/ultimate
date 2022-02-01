(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)


(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun I () SetOfInt)
(declare-fun J () SetOfInt)

; I is the set of Int resp. Nat numbers

; 337, 1916 / out of memory
;(assert (exists ((I SetOfInt)) (forall ((x Int)) (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J)) ))))

; 341, 1959 / out of memory (100 gigabyte)
;(assert (forall ((x Int)) (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J)) )))

; 8, 43 / 79, 971
;(assert (exists ((y Int)) (and (element y I) (= x y) (subsetInt I J))))

; 6, 35 / 60, 606
;(assert (and (element y I) (= x y) (subsetInt I J)))

; 6, 24 / 60, 409
;(assert (and (element y I) (= x y)))

; 2, 7 / 6, 39
;(assert (and (element y I) (subsetInt I J)))

; 7, 45 / 42, 450
;(assert (and (= x y) (subsetInt I J)))

; 1, 3 / 1, 3
;(assert (subsetInt I J))

; 7, 15 / 42, 150
(assert (= x y))

; 2, 5 / 8, 34
;(assert (element y I))

(check-sat)
