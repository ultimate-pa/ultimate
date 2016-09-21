(set-logic QF_UFLIRA)
(set-info :source |
Alberto Griggio

|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(assert (and (not (>= (+ (* x4 2) (+ (* x7 (- 2)) (* x8 (- 2)))) 2)) (and (and (not (<= 1 x4)) (<= (+ (+ (+ (- x3) x8) (* x4 (- 2))) x7) (- 1))) (<= (+ (+ x3 x8) x7) 0))))
(check-sat)
(exit)
