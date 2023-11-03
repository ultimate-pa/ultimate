(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)

(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )))

(declare-const a List)
(declare-const b List)

(assert (and (= a (cons zero b)) ((_ is cons) b) (= (cdr b) a)))
(check-sat)
(get-proof)
