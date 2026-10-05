; Fresh-value collision, predicate variant: no numeric function values enter
; LA, so the only registered numeric value is a = 2. The CC-local x gets the
; fresh value 3, which collides with the unregistered use-site value a+1 = 3,
; making p(3) both true and false.
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-info :status sat)
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun x () Int)
(declare-fun p (Int) Bool)
(assert (>= a 2))
(assert (p (+ a 1)))
(assert (not (p x)))
(check-sat)
(get-model)
(get-value (a x (p (+ a 1)) (p x)))
