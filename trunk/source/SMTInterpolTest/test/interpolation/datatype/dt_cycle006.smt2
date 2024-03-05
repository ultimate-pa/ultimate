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

(assert (! (and (and (= (car w) r) (= (cdr u) s) ((_ is cons) w)) ((_ is cons) u)) :named A))
(assert (! (and (and (= r v) (= t u)) (= s (cons q p))) :named B))
(assert (! (and (and (and (and (and (= (cdr v) t) (= (cdr u) t)) (= (car p) w)) ((_ is cons) v)) ((_ is cons) t)) ((_ is cons) p)) :named C))

(check-sat)
(get-interpolants A B C)
(get-interpolants C B A)
(get-interpolants B C A)
(exit)
