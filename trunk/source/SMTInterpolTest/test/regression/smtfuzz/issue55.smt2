(set-logic LIA) 
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(assert (forall ((q0 Bool) (q1 Bool)) (not (xor q1 v1 v0 q0 q1 (> 100 13) v0 q1))))
(push 1)
(assert (=> v1 v1))
(pop 1)
(check-sat)

