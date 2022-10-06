(set-option :produce-models true)
(set-logic QF_AUFLIA)

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const v Int)

(assert (= (@diff a b) 2))
(assert (not (= a b)))
(assert (= (@diff (store a 1 v) b) 3))

(check-sat)
(get-model)

