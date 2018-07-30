; Test identification of basic term types
(set-logic UFLIA)

; MoNatDiff specific declarations
(declare-sort SetOfInts 0)
(declare-fun element (Int SetOfInts) Bool)
(declare-fun subsetInts (SetOfInts SetOfInts) Bool)
(declare-fun strictSubsetInts (SetOfInts SetOfInts) Bool)

(declare-fun x () Int)
(declare-fun S () SetOfInts)

(assert (x))
(assert (S))

(check-sat)
(get-model)
