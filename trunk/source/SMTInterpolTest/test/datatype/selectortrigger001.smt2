(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_UFDTLIA)
(set-info :status unsat)
(declare-datatypes ((Pair 0)) (((mk (f1 Int) (f2 Int)))))
(declare-fun x () Pair)
(declare-fun y () Pair)
(declare-fun w () Int)
; All selector applications of mk exist for x and for y, so rule 5 has to create the testers and rule 3 the
; constructor terms mk(f1 x, f2 x) and mk(f1 y, f2 y).  Only then are the field values arguments of a constructor
; application, which is what makes the model-based theory combination compare them.  Since y is pinned to 0 by w,
; both fields agree and x and y are equal after all.
(assert (not (= x y)))
(assert (= (f1 x) (f1 y)))
(assert (= (f2 x) 0))
(assert (= (+ (f2 y) w) 0))
(assert (<= w 0))
(assert (<= 0 w))
(check-sat)
(get-proof)
(exit)
