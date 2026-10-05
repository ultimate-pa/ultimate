; Fresh-value collision with an offset use-site: x is CC-local (never enters
; LA), so the model builder assigns it a "fresh" value larger than all used
; values. But "used" only tracks values registered for CCTerm representatives;
; the use-site value of the argument a+1 (= value(a) + offset 1) is never
; registered. With a = 2 the fresh value for x is 3 = a+1, so f is evaluated
; at the same point twice with different results.
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-info :status sat)
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun x () Int)
(declare-fun f (Int) Int)
(assert (>= a 2))
(assert (not (= (f (+ a 1)) (f x))))
(check-sat)
(get-model)
(get-value (a x (f (+ a 1)) (f x)))
