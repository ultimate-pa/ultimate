(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun I () SetOfInt)


(assert (exists ((I SetOfInt) (x Int))  (and (=> (element x I) (element (+ x 1) I)) (= (- x y) 0) (element x I) (= x 5) )))
;(assert (exists ((x Int)) (exists ((I SetOfInt)) (and (=> (element x I) (element (+ x 1) I)) (= (- x y) 0) (element x I) (= x 5) ))))
;(assert  (and (= (- x y) 0) (element x I) (= x 5) ))

; x = 5 && y = x && (x in I => x+1 in I)  
;(assert (= (- x y) 0) )

;(assert (exists ((I SetOfInt)) (and (=> (element x I) (element (+ x 1) I)) (= (- x y) 0) (element x I) (= x 1) )))



;(assert (< (- x y) 1))

(check-sat)
(get-value (y))
