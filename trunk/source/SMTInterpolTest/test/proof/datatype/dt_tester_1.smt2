(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car U) (cdr List) ))
))
(declare-const x List)
(declare-const y U)

(assert (= x (cons y nil)))
(assert (not ((_ is cons) x)))
(check-sat)
(get-proof)
