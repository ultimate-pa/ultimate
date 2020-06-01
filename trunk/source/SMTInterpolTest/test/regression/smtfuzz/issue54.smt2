(set-logic BV)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v10 () Bool)
(assert (not (exists ((q0 Bool) (q1 Bool) (q2 Bool) (q3 Bool)) (not (xor v3 q3 v10 v2 q3)))))
(check-sat)

