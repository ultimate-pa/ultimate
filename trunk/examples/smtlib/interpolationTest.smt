(benchmark interpolationTest
:source {
Desired Interpolant: (and (= ab3 ab2) (= ab (g ab1)))
}
:category { crafted }
:difficulty { 0 }
:logic QF_UF
:extrafuns ((a U) (a2 U) (a3 U) (b U) (b2 U) (b3 U) (ab U) (ab1 U) (ab2 U) (ab3 U) (fa U U) (fb U U) (g U U))
:notes "Interpolation Problem starts here"
:assumption
 (and (= a ab) (= a (g ab1)) (= ab2 a2) (= a2 ab3))
:formula
 (and (= ab1 b2) (= b2 (fb ab2)) (= (fb ab3) (g ab1))
      (= ab1 b3) (not (= b3 ab)))
)
