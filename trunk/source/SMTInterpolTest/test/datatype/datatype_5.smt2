(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)

(assert (and (= u (cons zero nil)) (= v (cons (succ zero) nil)) (= u v)))

(check-sat)
(exit)
