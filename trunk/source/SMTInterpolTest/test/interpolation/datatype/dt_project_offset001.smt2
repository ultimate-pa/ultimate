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
(declare-const s D)
(declare-const bs D)
(declare-fun p (Int) Bool)

;; projection on a shifted constructor argument: bs = s = mk(a+5) gives via
;; dt-project the offset equality val(bs) = a+5, which then justifies the
;; congruence p(a+10) = p(val(bs)+5) with shift 5.

(assert (! (and (= (mk (+ a 5)) s) (p (+ a 10))) :named A ))
(assert (! (and (= s bs) (not (p (+ (val bs) 5)))) :named B ))

(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
