(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

(assert (= (div x 0) 5))
(assert (= (div y 0) 3))
(check-sat)
(get-model)
