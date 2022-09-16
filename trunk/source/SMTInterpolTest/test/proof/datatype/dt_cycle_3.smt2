(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)


(assert (and (= u (cons zero (cons zero v))) (= (cdr v) u) (not ((_ is nil) v)) ))

(check-sat)
(get-proof)
