(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_UFDTLIA)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car Int) (cdr List) ))
))

(declare-const a Int)
(declare-const u List)
(declare-const v List)
(declare-const w List)
(declare-fun p (List) Bool)


(assert (! (= u (cons (+ (car u) 1) v)) :named A))
(assert (! (= v w) :named B))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)

(exit)
