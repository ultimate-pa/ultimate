; Fresh-value collision with the offset on the CC-local side: the fresh value
; chosen for x must keep the use-site value x-1 distinct from all other
; f-argument values, i.e. the fresh value must account for the parameter's
; negative offset. Here LA mutates a to 1 and the fresh x = 2 gives x-1 = 1 = a.
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-info :status sat)
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun x () Int)
(declare-fun f (Int) Int)
(assert (>= a 0))
(assert (not (= (f a) (f (- x 1)))))
(check-sat)
(get-model)
(get-value (a x (f a) (f (- x 1))))
