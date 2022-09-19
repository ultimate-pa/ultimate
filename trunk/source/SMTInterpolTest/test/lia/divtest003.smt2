(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

(assert (= (div x 2) 5))
(assert (= (div y 3) 3))
(check-sat)
(get-model)
