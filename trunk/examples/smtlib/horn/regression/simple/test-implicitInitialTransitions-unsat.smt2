; status: unsat (checked by z3)
; written on 27.03.2017 (condensed on 7.8.2017)
; currently, we say this set is sat without looking at any trace, because the "initial transitions" 
; don't have the form of an implication withough uninterpreted predicates in the body.
; author: nutz@informatik.uni-freiburg.de
(set-info :status unsat)
(set-logic HORN)

(declare-fun I (Int) Bool)

(assert (I 0)) ; equivalent to "(=> (= x 0) (I_x x))", but not translated like that right now..

(assert (forall ((x Int)) (=> (and (I x) (= x 0)) false)))

(check-sat)
