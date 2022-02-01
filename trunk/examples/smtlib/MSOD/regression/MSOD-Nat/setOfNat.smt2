(set-logic UFLIA)
(set-info :status sat)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

; I is the set of Nat numbers.
(assert (forall ((x Int))  (element x I)))

(check-sat)
