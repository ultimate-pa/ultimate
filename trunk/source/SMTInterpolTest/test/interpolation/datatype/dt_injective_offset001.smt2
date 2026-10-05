(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_UFDTLIA)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (D 0) ) (
 ( (mk (val Int)) )
))

(declare-const a Int)
(declare-const b Int)
(declare-const s D)
(declare-fun p (Int) Bool)

;; injectivity on shifted constructor arguments: mk(a+5) = s = mk(b+7)
;; gives the offset equality a+5 = b+7 (canonically b = a-2), which then
;; justifies the congruence p(a+3) = p(b+5) with shift -2.

(assert (! (and (= (mk (+ a 5)) s) (p (+ a 3))) :named A ))
(assert (! (and (= s (mk (+ b 7))) (not (p (+ b 5)))) :named B ))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
