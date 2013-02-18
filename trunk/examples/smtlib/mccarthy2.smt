(benchmark mccarthy1.smt
:source {
This is the example in Figure 4 and Figure 9 of the paper

 M. Heizmann, J.Hoenicke, A.Podelski, Nested Interpolants, POPL 2010

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
Interpolant 3: (not (<= x2 100))
Interpolant 4: (and (not (<= (+ (* 1 x2) (* (~ 1) res4)) 9)) (<= (+ (* 1 x2) (* (~ 1) res4)) 10) (not (<= x2 100)))

}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrafuns ((x_1    Int))
:extrafuns ((xm1    Int))
:extrafuns ((x2     Int))
:extrafuns ((res4   Int))
:assumption
(<= x_1 100)
:assumption
(= xm1 (+ x_1 11))
:assumption
(= x2 xm1)
:assumption
(> x2 100)
:assumption
(= res4 (- x2 10))
:formula
(and (<= x2 101) (distinct res4 91))
)
