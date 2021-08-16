(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status sat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (= zero (match u ((nil zero) (x (car x))))))
(assert (not (= u nil)))
(assert ((_ is nil) (cdr u)))

(check-sat)
