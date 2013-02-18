(benchmark mccarthy1.smt
:source {
This is the example in Figure 6 of the paper

 M. Heizmann, J.Hoenicke, A.Podelski, Nested Interpolants, POPL 2010

This computes the interpolants omitting the two calls.

Desired Interpolants: 
   x_1    <= 100,
   xm1    <= 111,
   resm5  <= 101
   xm6    <= 101
   resm10 != 91
   res11  != 91 

Actual Interpolants:
(mainly because x_1 <= 100 is regarded as B literal)
Interpolant 0: (<= x_1 100)
Interpolant 1: (and (not (<= (+ (* 1 x_1) (* (~ 1) xm1)) (~ 12))) (<= x_1 100))
Interpolant 2: (and (<= resm5 (+ x_1 1)) (<= x_1 100))
Interpolant 3: (and (<= xm6 (+ x_1 1)) (<= x_1 100))
Interpolant 4: (and (<= (+ resm10 9) x_1) (<= 91 resm10) (<= x_1 100))
Interpolant 5: (and (<= (+ res11 9) x_1) (<= 91 res11) (<= x_1 100))

}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrafuns ((x_1    Int))
:extrafuns ((xm1    Int))
:extrafuns ((x2     Int))
:extrafuns ((res4   Int))
:extrafuns ((resm5  Int))
:extrafuns ((xm6    Int))
:extrafuns ((x7     Int))
:extrafuns ((res9   Int))
:extrafuns ((resm10 Int))
:extrafuns ((res11  Int))
:assumption
(<= x_1 100)
:assumption
(= xm1 (+ x_1 11))
:assumption
(and (= x2 xm1)
     (> x2 100)
     (= res4 (- x2 10))
     (= resm5 res4))
:assumption
(= xm6 resm5)
:assumption
(and (= x7 xm6)
     (> x7 100)
     (= res9 (- x7 10))
     (= resm10 res9))
:assumption
(= res11 resm10)
:formula
(and (<= x_1 101) (distinct res11 91))
)
