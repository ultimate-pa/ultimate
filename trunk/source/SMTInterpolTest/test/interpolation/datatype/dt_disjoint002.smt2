(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons2 (car2 Nat) (cdr2 List)) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)
(declare-const w List)

(declare-const a1 Nat)
(declare-const a2 List)
(declare-const b1 Nat)
(declare-const b2 List)

;; disjoint

(assert (! (= u (cons a1 a2)) :named A ))
(assert (! (= v (cons2 b1 b2)) :named B )) 
(assert (! (= u v) :named C ))

(check-sat)
(get-interpolants A B C)
(get-interpolants C B A)
(get-interpolants B C A)
(get-interpolants C A B)
(get-interpolants A C B)

(exit)
