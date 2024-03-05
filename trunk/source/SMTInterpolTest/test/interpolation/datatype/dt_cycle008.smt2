(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_UFDT)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)

;; simple cycle

(assert (! (= u (cons zero (cons zero v))) :named A))
(assert (! (= v (cons (succ zero) u)) :named B))


(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
