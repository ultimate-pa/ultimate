(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (= zero (match u ((nil zero) (x (succ (car x)))))))
(assert (not (= u nil)))

(check-sat)
