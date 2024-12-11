(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_UFDT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const a Nat)
(declare-const u List)
(declare-const v List)
(declare-const w List)
(declare-fun p (List) Bool)


(assert (! (= v (cons a w)) :named A))
(assert (! (p (cdr v)) :named B))
(assert (! (not (p w)) :named C))

(check-sat)
(get-interpolants A B C)
(get-interpolants B C A)
(get-interpolants C A B)
(get-interpolants C B A)
(get-interpolants A C B)
(get-interpolants B A C)

(exit)
