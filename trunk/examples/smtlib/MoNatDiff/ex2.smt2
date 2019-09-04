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



;(assert (exists ((x Int) (< x 0)))) Parser checken
(assert (exists ((x Int)) (< x 1)))
;(assert (< z 2))
;(assert (=> (< x 5) (< y 4) (< z 3)))
;(assert (=> (< x 1) (< y 2)))
;(assert (not (< x 1)))
;(assert (< x 1))


;(assert (not (or (< x 2) (< y 2))) )
;(assert (exists ((x Int)) (not (and (< x 2) (< y 2)))) )
;(assert (not (exists ((x Int)) (not (and (< x 2) (< y 2))))) )
;(assert (forall ((x Int)) (and (< x 2) (< y 2))) )

;(assert (exists ((y Int)) (and (< (- y x) 2) (not (< y 3)))))
;(assert (exists ((y Int)) (and (<= (- x y) 2) (<= y 2))))
;(assert (exists ((x Int) (y Int)) (and (< x 3) (< (- y z) 3))))
;(assert (exists ((x Int)) (exists ((y Int)) (and (< x 3) (< (- y z) 3)))))

;(assert (and (not (< x 2)) (< y 2) (not (< y 1)) (element x S) (element y S)))
;(assert (and (not (> x 0)) (< y 0) (element x S) (element y S)))
;(assert (not (element 0 S)))

;(assert (exists ((x Int)) (not (element (+ x 0) S))))
;(assert (< x 3))

;(assert (< (- x) 0))

;(assert (not (element (+ x 0) S)))

;(assert (exists ((S SetOfInt)) (and (element (+ x 0) S) (<= (- x y) 1))))

(check-sat)
(get-model)
