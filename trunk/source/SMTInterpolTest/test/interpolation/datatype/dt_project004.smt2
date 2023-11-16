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

(declare-const r List)
(declare-const s List)
(declare-const t List)
(declare-const u List)
(declare-const v List)
(declare-const w List)

(assert (! (and (= t u) (= u (cons zero w))) :named A ))
(assert (! (= r w) :named B ))
(assert (! (and (= s t) (not (= (cdr s ) r))) :named C ))
(assert (! (= u s) :named D ))

(check-sat)
(get-interpolants A B C D)
(get-interpolants D C B A)
(get-interpolants C A D B)
(get-interpolants A D B C)
(exit)
