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
(declare-const b Nat)
(declare-const z Nat)
(declare-const u List)
(declare-const v List)
(declare-const w List)
(declare-const t List)
(declare-fun f (List) Nat)

;; injective

(assert (! (= (cons a u) w) :named A ))
(assert (! (not (= (f u) z)) :named B ))
(assert (! (= z (f v)) :named C ))
(assert (! (= (cons b v) w) :named D )) 

(check-sat)
(get-interpolants A B C D)
(get-interpolants D A B C)
(get-interpolants C D A B)
(get-interpolants B C D A)
(get-interpolants D C B A)
(get-interpolants A D C B)
(get-interpolants B A D C)
(get-interpolants C B A D)
(exit)
