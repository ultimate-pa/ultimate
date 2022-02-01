(set-option :produce-proofs true)
(set-info :source "{
This is the example in Figure 6 of the paper

 M. Heizmann, J. Hoenicke, A. Podelski, Nested Interpolants, POPL 2010

This computes the interpolants omitting the two calls.

Desired Interpolants: call 1
   x_1    <= 100,
   xm1    <= 111,
   resm5  <= 101
   xm6    <= 101
   resm10 == 91
   res11  == 91 

Actual Interpolants:
Interpolant 0: (<= x_1 100)
Interpolant 1: (<= xm1 111)
Interpolant 2: (<= resm5 101)
Interpolant 3: (<= xm6 101)
Interpolant 4: (and (<= 0 (+ resm10 (- 91))) (<= resm10 91))
Interpolant 5: (and (<= 0 (+ res11 (- 91))) (<= res11 91))

Desired Interpolants: call 2
   true, res4 <= x2 - 10

Actual Interpolants:
Interpolant 0: true
Interpolant 1: (<= res4 (+ x2 (- 10)))

Desired Interpolants: call 3
   x7 >= 101, x7 >= 101 && res9 = x7 - 10

Actual Interpolants:
Interpolant 0: (<= 0 (+ x7 (- 101)))
Interpolant 1: (and (<= 0 (+ res9 (- 91))) (<= res9 (+ x7 (- 10))))

}")
(set-info :status unsat)
(set-info :difficulty "{ 0 }")
(set-logic QF_UFLIA)
(declare-fun x_1 () Int)
(declare-fun xm1 () Int)
(declare-fun x2 () Int)
(declare-fun res4 () Int)
(declare-fun resm5 () Int)
(declare-fun xm6 () Int)
(declare-fun x7 () Int)
(declare-fun res9 () Int)
(declare-fun resm10 () Int)
(declare-fun res11 () Int)
(assert (! (<= x_1 100) :named IP_0))
(assert (! (= xm1 (+ x_1 11)) :named IP_1))
(assert (! (= x2 xm1) :named IP_2))
(assert (! (> x2 100) :named IP_3))
(assert (! (= res4 (- x2 10)) :named IP_4))
(assert (! (= resm5 res4) :named IP_5))
(assert (! (= xm6 resm5) :named IP_6))
(assert (! (= x7 xm6) :named IP_7))
(assert (! (> x7 100) :named IP_8))
(assert (! (= res9 (- x7 10)) :named IP_9))
(assert (! (= resm10 res9) :named IP_10))
(assert (! (= res11 resm10) :named IP_11))
(assert (! (and (<= x_1 101) (distinct res11 91)) :named IP_12))
(check-sat)
(get-interpolants IP_0 IP_1 (IP_2 IP_3 IP_4 IP_5) IP_6 
                  (IP_7 IP_8 IP_9 IP_10) IP_11 IP_12)
(exit)
