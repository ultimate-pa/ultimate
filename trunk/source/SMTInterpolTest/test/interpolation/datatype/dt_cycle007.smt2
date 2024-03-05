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
(declare-const r List)
(declare-const q List)
(declare-const p List)

;;cycle

(assert (! (= t w) :named A))
(assert (! ((_ is cons) w) :named B))
(assert (! (= (car w) r) :named C))
(assert (! (= r (cons u u)) :named D))
(assert (! ((_ is cons) u) :named E))
(assert (! (= (cdr u) t) :named F))

(check-sat)
(get-interpolants A B C D E F)
(get-interpolants F E D C B A)
(get-interpolants D E F A B C)
(get-interpolants C B A F E D)
(get-interpolants D (A B (E F)) C)
(exit)
