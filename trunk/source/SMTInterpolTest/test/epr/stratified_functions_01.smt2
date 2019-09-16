; test to check how epr in SmtInterpol handles stratified functions

(set-option :print-success false)
(set-option :produce-proofs false)


(set-logic UF)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort V 0)
(declare-sort W 0)
(declare-const v1 V)
(declare-const w1 W)
(declare-fun f (V) W)
(declare-fun P (V) Bool)
(declare-fun Q (W) Bool)

(assert (forall ((x V)) (=> (P x) (Q (f x)))))
(assert (= (f v1) w1))
(assert (P v1))
(assert (not (Q w1)))

(check-sat)
