(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDTLIA)
(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car Int) (cdr List) ))
))
(declare-const x List)
(declare-const y Int)

(assert (= x (cons y nil)))
(assert (= (+ 1 (car x)) y))
(check-sat)
(get-proof)
