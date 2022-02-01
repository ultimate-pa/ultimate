(benchmark abmixed2int.smt
:source {
Test formula which needs AB-mixed interpolators
Desired Interpolant: (and (<= y x1) (implies (>= y x1) (< (f (- x1 5)) x2)))
}
:status unsat
:difficulty { 0 }
:logic AUFLIRA
:extrafuns ((a1 Int))
:extrafuns ((a2 Int))
:extrafuns ((b1 Int))
:extrafuns ((b2 Int))
:extrafuns ((x1 Int))
:extrafuns ((x2 Int))
:extrafuns ((y Int))
:extrafuns ((f Int Int))
:assumption
(and (<= a1 x1) (and (= (f (+ a1 5)) a2) (and (<= y a1) (< a2 x2))))
:formula
(and (<= x1 (- b1 12)) (and (= (f (- b1 7)) b2) (and (<= (- b1 12) y) (< x2 b2)))))
