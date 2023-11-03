(set-info :smt-lib-version 2.6)
(set-logic LIA)
(declare-fun hi () Int)
(declare-fun lo () Int)
(declare-fun y () Int)
(declare-fun z () Int)
; we can eliminate x but have to add a divisibiliy constraint
(simplify (exists ((x Int)) (and (= (* 7 x) y ) (= (* 5 x) z))))
; quantified variables have coefficients that are not a divisor of other 
; coefficients of the same linear inequality
(simplify (exists ((x Int)) (and (<= (* 7 x) hi ) (<= lo (* 5 x)))))
