(set-info :smt-lib-version 2.6)
; the match term is not exhaustive
(set-info :expect-errors 1)
(set-logic QF_DT)

(set-info :category "crafted")


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (match u ((nil false) ((cons y) true))))
(assert (not ((_ is cons) u)))

(check-sat)
