(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInts 0)
(declare-fun element (Int SetOfInts) Bool)
(declare-fun subsetInts (SetOfInts SetOfInts) Bool)
(declare-fun strictSubsetInts (SetOfInts SetOfInts) Bool)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (exists ((y Int)) (and (<= (- x y) 2) (<= y 2))))

(check-sat)
(get-model)
