(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

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

;;cycle
(assert (! (and (= u (cons zero (cons zero v))) (= (cons zero v) (cons zero v))) :named A))
(assert (! (= v (cons (succ zero) u)) :named B))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
