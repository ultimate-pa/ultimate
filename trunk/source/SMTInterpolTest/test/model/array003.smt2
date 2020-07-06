(set-option :model-check-mode true)
(set-logic QF_ALIA)

(declare-const i Int)
(declare-const j Int)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const c (Array Int Int))

(assert (= (store b j 0) (store a i 0)))
(check-sat)
(get-model)
(get-value ((store b j 0) (store a i 0)))
