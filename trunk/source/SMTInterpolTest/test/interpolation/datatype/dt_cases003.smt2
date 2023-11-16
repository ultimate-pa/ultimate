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

(declare-const r List)
(declare-const s List)
(declare-const t List)
(declare-const u List)
(declare-const v List)
(declare-const w List)

(assert (! (and (= t u) (not ((_ is cons) u)) ) :named A ))
(assert (! (and (= s t) (not ((_ is cons2) s)) ) :named B ))
(assert (! (and (not ((_ is cons3) t)) (= r w)) :named C ))
(assert (! (and (not ((_ is nil) s)) (= u s)) :named D ))

(check-sat)
(get-interpolants A B C D)
(get-interpolants D A C B)
(get-interpolants A D C B)
(get-interpolants B C D A)
(get-interpolants D C B A)
(exit)
