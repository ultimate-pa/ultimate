(set-option :produce-proofs true)
(set-info :source "{
A Fast Linear-Arithmetic Solver for DPLL(T) by Bruno Dutertre and Leonardo de 
Moura
}")
(set-info :status unsat)
(set-info :difficulty "{ 0 }")
(set-logic AUFLIRA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (<= 1 (- (* 3 x) (* 3 y))) :named IP_0))
(assert (! (<= (- (* 3 x) (* 3 y)) 2) :named IP_1))
(check-sat)
(get-interpolants IP_0 IP_1)
(exit)
