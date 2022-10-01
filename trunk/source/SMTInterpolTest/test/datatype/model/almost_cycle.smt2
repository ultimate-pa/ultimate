(set-option :produce-models true)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status sat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)

(assert (and (= u (cons zero (cons zero v))) (= (cdr v) u) ))

(check-sat)
(get-model)
(get-value (u (cons zero v) (car nil) (cdr nil)))
(exit)
