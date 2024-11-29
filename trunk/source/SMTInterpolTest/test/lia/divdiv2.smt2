(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)

(set-info :status sat)
(assert (not (= (div (div x 3) 0) (div x (* 3 0)))))
(check-sat)
(get-model)
