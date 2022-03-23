(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) (Nat 0) (Cases 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
 ( (left (leftval Nat)) (right (rightval Nat)) )
))
(declare-const x0 Cases)
(declare-const x1 Cases)

(assert ((_ is right) x0))
(assert ((_ is left) x1))
(assert (= x0 x1))
(check-sat)
(get-proof)