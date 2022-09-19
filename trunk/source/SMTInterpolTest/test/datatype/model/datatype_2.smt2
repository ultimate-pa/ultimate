(set-option :produce-models true)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status sat)


(declare-datatypes ( (List 0) (Nat 0)) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)

(assert (and (= (cdr u) nil) (not ((_ is nil) u)) (= (car v) (succ zero)) (= u v) ))
(check-sat)
(get-model)
(exit)
