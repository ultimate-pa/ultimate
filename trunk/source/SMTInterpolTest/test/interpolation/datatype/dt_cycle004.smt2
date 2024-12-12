(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car List) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)
(declare-const w List)
(declare-const t List)
(declare-const s List)

;;cycle
(assert (! (and (and (= u (cons (cons s v) nil)) (= (cdr w) t)) ((_ is cons) w)) :named A))
(assert (! (and (= v (cons nil w)) (= u (cons nil t))) :named B))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
