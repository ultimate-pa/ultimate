(benchmark mccarthy1.smt
:source {
This is the example in Figure 6 of the paper

 M. Heizmann, J.Hoenicke, A.Podelski, Nested Interpolants, POPL 2010

This computes the interpolants starting with the second method call.

Desired Interpolants: 
   true,
   x7 >= 101,
   res9 = x7 - 10 && x7 >= 101
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
(> x7 100)
:assumption
(= res9 (- x7 10))
:assumption
(and (and (<= xm6 (+ x_1 1)) (<= x_1 100))
     (= x7 xm6)
     (= resm10 res9))
:assumption
(= res11 resm10)
:formula
(and (<= x_1 100) (distinct res11 91))
)
