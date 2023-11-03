(set-option :produce-models true)
(set-logic QF_AUFLIA)

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (= (@diff a b) 2))
(assert (not (= a b)))

(check-sat)
(get-model)

