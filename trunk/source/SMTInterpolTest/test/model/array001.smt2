(set-option :model-check-mode true)
(set-logic QF_ALIA)

(declare-const i Int)
(declare-const a (Array Int Int))

(assert (distinct (store a i 0) a))
(check-sat)
(get-model)
