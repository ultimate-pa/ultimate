(set-option :produce-interpolants true)
(set-info :source |
This is the example in Figure 4 and Figure 9 of the paper

 M. Heizmann, J. Hoenicke, A. Podelski, Nested Interpolants, POPL 2010

The interpolants of pi_3

Desired Interpolants: 
   true
   true
   true
   x2 >= 101
   res4 = x2 - 10 && x2 >= 101

Actual Interpolants:
Interpolant 0: true
Interpolant 1: true
Interpolant 2: true
Interpolant 3: (<= 0 (+ x2 (- 101)))
Interpolant 4: (and (<= res4 (+ x2 (- 10))) (<= 0 (+ res4 (- 91))))

|)
(set-info :status unsat)
(set-logic QF_UFLIA)
(declare-fun x_1 () Int)
(declare-fun xm1 () Int)
(declare-fun x2 () Int)
(declare-fun res4 () Int)
(assert (! (<= x_1 100) :named IP_0))
(assert (! (and (<= xm1 (+ x_1 11)) (>= xm1 (+ x_1 11))) :named IP_1))
(assert (! (and (<= x2 xm1) (>= x2 xm1)) :named IP_2))
(assert (! (> x2 100) :named IP_3))
(assert (! (and (<= res4 (- x2 10)) (>= res4 (- x2 10))) :named IP_4))
(assert (! (and (<= x2 101) (or (< res4 91) (> res4 91))) :named IP_5))
(check-sat)
(get-interpolants IP_0 IP_1 IP_2 IP_3 IP_4 IP_5)
(exit)
