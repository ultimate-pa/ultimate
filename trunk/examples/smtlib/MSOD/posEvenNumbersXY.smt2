(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun I () SetOfInt)

; I contains all positive even numbers including 0. Result: sat (*Buchi), unsat (*Weak)
(assert (element 0 I))

(assert (forall ((x Int)) (=> (element x I) (and (element (+ x 2) I) (>= x 0) (not (element (+ x 1) I))))))

(assert (forall ((x Int)) (exists ((y Int)) () )))

(check-sat)
(get-value (I))
