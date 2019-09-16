; test to check how epr in SmtInterpol handles stratified functions

(set-option :print-success false)
(set-option :produce-proofs false)


(set-logic UF)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort V 0)
(declare-sort W 0)
(declare-const v1 V)
(declare-fun f (V) W)
(declare-fun P (V) Bool)
(declare-fun Q (W) Bool)

(assert (forall ((x V)) (=> (P x) (Q (f x)))))
(assert (forall ((x W)) (not (Q x))))
(assert (P v1))

(check-sat)
