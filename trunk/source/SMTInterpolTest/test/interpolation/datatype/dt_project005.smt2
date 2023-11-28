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


(assert (! (= u (cons a w)) :named A))
(assert (! (= u v) :named B))
(assert (! (p (cdr v)) :named C))
(assert (! (not (p w)) :named D))

(check-sat)
(get-interpolants A B C D)
(get-interpolants D A B C)
(get-interpolants C D A B)
(get-interpolants B C D A)
(get-interpolants D C B A)
(get-interpolants A D C B)
(get-interpolants B A D C)
(get-interpolants C B A D)
(get-interpolants A C B D)
(get-interpolants D A C B)
(get-interpolants B D A C)
(get-interpolants C B D A)
(get-interpolants D B C A)
(get-interpolants A D B C)
(get-interpolants C A D B)
(get-interpolants B C A D)

(exit)
