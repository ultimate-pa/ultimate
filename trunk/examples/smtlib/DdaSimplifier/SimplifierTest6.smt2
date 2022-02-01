(set-logic QF_UFLIA)
(set-info :author pomrehn@informatik.uni-freiburg.de)
(set-info :category "crafted")
(set-info :status sat)
(set-info :source "{ Test where the while loop of the DDA simplifier is executed 3 times in a single procedure call.
(not (= x 1)) is not redundant because it is not implied by the other concunct.
(= x 1) on the right hand side is non-relaxing, because it is implied by its critical constraint. It is simlified to false.
Afterwards (not (= x 1)) is non-constraining and therefore simplified to true.}")
(set-option :strong-context-simplifier true)
(declare-fun x () Int)
(simplify (and (not (= x 1)) (or (<= x 0) (> x 2) (= x 1))))
(exit)