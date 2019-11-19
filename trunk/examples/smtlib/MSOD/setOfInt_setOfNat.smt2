(set-logic UFLIA)

(declare-sort SetOfInt 0)
(declare-fun element (Int SetOfInt) Bool)
(declare-fun subsetInt (SetOfInt SetOfInt) Bool)
(declare-fun strictSubsetInt (SetOfInt SetOfInt) Bool)

(declare-fun x () Int)
(declare-fun I () SetOfInt)

; I is the set of Int/Nat numbers. Result: sat (IntBuchi, NatBuchi), unsat (IntWeak, NatWeak)
(assert (forall ((x Int))  (element x I)))

(check-sat)
(get-value (I))
