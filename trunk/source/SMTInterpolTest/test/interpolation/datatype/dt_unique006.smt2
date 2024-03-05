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

;; unique

(assert (! (= u v) :named A ))
(assert (! (= u w) :named B )) 
(assert (! ((_ is cons) v) :named C ))
(assert (! ((_ is cons2) w) :named D ))  

(check-sat)
(get-interpolants A B C D)
(get-interpolants D A C B)
(get-interpolants C D A B)
(get-interpolants B C D A)
(get-interpolants C A B D)
(get-interpolants D B A C)
(exit)
