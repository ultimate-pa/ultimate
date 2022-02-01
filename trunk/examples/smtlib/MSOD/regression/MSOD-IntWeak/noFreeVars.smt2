(set-logic UFLIA)
(set-info :status sat)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

; there exists a Set I and an Integer x s.t. x=5 and x in I and if x is in I then so is x + 1.
(assert (exists ((I SetOfInt) (x Int))  (and (=> (element x I) (element (+ x 1) I)) (element x I) (= x 5) )))

(check-sat)
