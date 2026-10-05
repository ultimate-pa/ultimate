; Datatype lemmas over a numeric constructor field must respect offset equalities.
; dt-project: from u = mk(y+5) the selector f(u) must equal y+5 (not y).
; dt-injective: from mk(y+5) = mk(z) the argument equality y+5 = z must be propagated.
(set-info :smt-lib-version 2.6)
(set-logic QF_UFDTLIA)
(set-info :status unsat)
(declare-datatype P ((mk (f Int))))
(declare-fun u () P)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= u (mk (+ y 5))))
(assert (= (mk (+ y 5)) (mk z)))
; f(u) = y+5 (dt-project) and z = y+5 (dt-injective); both contradict the disjunction below
(assert (or (not (= (f u) (+ y 5))) (not (= z (+ y 5)))))
(check-sat)
