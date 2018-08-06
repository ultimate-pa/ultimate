(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun S () SetOfInt)

;(assert (not (and (< x 2) (< y 2))) )
;(assert (exists ((x Int)) (not (and (< x 2) (< y 2)))) )
;(assert (not (exists ((x Int)) (not (and (< x 2) (< y 2))))) )
(assert (forall ((x Int)) (and (< x 2) (< y 2))) )

;(assert (exists ((x Int) (y Int)) (< x y)))
;(assert (exists ((y Int)) (and (< (- y x) 2) (not (< y 3)))))
;(assert (exists ((y Int)) (and (<= (- x y) 2) (<= y 2))))
;(assert (exists ((x Int) (y Int)) (and (< x 3) (< (- y z) 3))))
;(assert (exists ((x Int)) (exists ((y Int)) (and (< x 3) (< (- y z) 3)))))
;(assert (and (not (< x 2)) (< y 2) (not (< y 1)) (element x S) (element y S)))
;(assert (not (element (+ x 0 ) S)))
;(assert (exists ((S SetOfInt)) (and (element (+ x 0) S) (<= (- x y) 1))))

(check-sat)
(get-model)
