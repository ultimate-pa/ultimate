(set-option :print-success false)
(set-logic UFLIA)
(set-info :source |E-matching with offset equalities: a and b share a congruence class
at offset 1 (b = a+1). The substitutions x := a and x := b are different values and
must not be conflated by the representative-based dedup; both instances are needed.|)
(set-info :status unsat)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= b (+ a 1)))
(assert (forall ((x Int)) (>= (f x) 0)))
(assert (< (+ (f a) (f b)) 0))
(check-sat)
(exit)
