(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)

(set-info :status sat)
(assert (not (= (div (div x 0) 5) (div x (* 0 5)))))
(check-sat)
(get-model)
