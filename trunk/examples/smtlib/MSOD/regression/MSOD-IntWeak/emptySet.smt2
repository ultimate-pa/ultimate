(set-logic UFLIA)
(set-info :status sat)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

; I is the empty set.
(assert (forall ((x Int))  (not (element x I))))

(check-sat)