;;; Processed by pysmt to remove constant-real bitvector literals
(set-logic QF_FP)
(set-info :source |SPARK inspired floating point problems by Florian Schanda|)
(set-info :smt-lib-version 2.0)
(set-info :category crafted)
;(set-info :status unsat)

(define-sort Float63 () (_ FloatingPoint 11 52))


(define-fun isFinite ((f Float32)) Bool (or (fp.isNormal f) (fp.isSubnormal f) (fp.isZero f)))
;(define-fun float__first () (_ FloatingPoint 11 52) ((_ to_fp 11 52) #xFF7FFFFF))
;(define-fun float__last () (_ FloatingPoint 11 52) ((_ to_fp 11 52) #x7F7FFFFF))
(declare-fun x () Float63)
;(assert (isFinite x))
(define-fun res () Float63 x)
;(assert (not (and (fp.geq res ((_ to_fp 11 53) RNE float__first)) (fp.leq res ((_ to_fp 11 53) RNE float__last)))))
(check-sat)
(exit)
