; checks if a hornclause with a constraint in the head that is not "false" 
; is treated properly
;
; unsat 
(set-info :status unsat)
(set-logic HORN)

(declare-fun I (Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (= x 1) (I x))))

(assert (forall ((x Int) (y Int)) (=> (I x) (= x 0))))

(check-sat)
;(get-model)
