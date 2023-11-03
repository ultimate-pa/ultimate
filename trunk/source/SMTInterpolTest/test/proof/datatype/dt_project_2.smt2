(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car U) (cdr List) ))
))
(declare-const x List)
(declare-const y U)

(assert (not (= (car (cons y nil)) y)))
(check-sat)
(get-proof)
