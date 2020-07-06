(set-option :model-check-mode true)
(set-logic QF_ALIA)

(declare-const i Int)
(declare-const a (Array Int Int))
(declare-const b (Array (Array Int Int) (Array Int Int)))

(assert (distinct (store a i 0) a))
(assert (distinct (store b a ((as const (Array Int Int)) 0)) b))
(assert (distinct (store b a a) b))
(check-sat)
(get-model)
(get-value (a (store a i 0) b (store b a a)))
