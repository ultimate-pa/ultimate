(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List)) (cons2 (car2 List) (cdr2 List)) (cons3 (car3 List) (cdr3 Nat)))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (! (and (not ((_ is nil) u)) (not ((_ is cons) u))) :named A ))
(assert (! (not ((_ is cons2) u)) :named B ))
(assert (! (not ((_ is cons3) u)) :named C ))

(check-sat)
(get-interpolants A B C)
(get-interpolants C B A)

(exit)
