(benchmark mccarthy1.smt
:source {
This is the example in Figure 6 of the paper

 M. Heizmann, J.Hoenicke, A.Podelski, Nested Interpolants, POPL 2010

This computes the interpolants starting with the first method call, ommitting
the second call.

Desired Interpolants: 
   true
   true
   resm5 <= 101
   xm6    <= 101
   resm10 != 91
   res11  != 91 
   
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
true
:assumption
(> x2 100)
:assumption
(= res4 (- x2 10))
:formula
(and (and (not (<= (+ (* 1 x_1) (* (~ 1) xm1)) (~ 12))) (<= x_1 100))
     (= x2 xm1)
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
(and (<= x_1 100) (distinct res11 91))
)
