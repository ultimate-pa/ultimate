(set-option :produce-proofs true)
(set-logic QF_LIA)
(declare-const x Int)

(set-info :status sat)
(assert (not (= (div (div x (- 3)) (- 5)) (div x (* (- 3) (- 5))))))
(check-sat)
(get-model)
