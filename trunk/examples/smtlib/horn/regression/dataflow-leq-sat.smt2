; 'reachable state space' seems to be:
; R: {(n, 0) | n >= 0}, 
; I: {(n+1, m) | (n, m) in R}, {(n+1, m+1) | (n, m) in I}, 
; the 'assertion' prohibits all states in I where m is three bigger than n 
; from the rules it follows that n is always bigger equal m, for any I(n, m)
; --> sat
(set-info :status sat)
(set-logic HORN)

(declare-fun I (Int Int) Bool)
(declare-fun R (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (R x y))))

(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (R x y) (= x1 (+ x 1))) (R x1 y))))
(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (R x y) (= x1 (+ x 1))) (I x1 y))))

(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (I x y) (= x1 (+ x 1)) (= y1 (+ y 1))) (I x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (I x y) (= y (+ x 3))) false)))


(check-sat)
;(get-model)
