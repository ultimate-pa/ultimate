(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInts 0)
(declare-fun element (Int SetOfInts) Bool)
(declare-fun subsetInts (SetOfInts SetOfInts) Bool)
(declare-fun strictSubsetInts (SetOfInts SetOfInts) Bool)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun S () SetOfInts)

(assert (exists ((S SetOfInts)) (and (element (+ x 0) S) (and (element (+ y 0) S) (<= y 2)))))

(check-sat)
(get-model)
