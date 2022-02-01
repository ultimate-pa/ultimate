(benchmark abmixed4.smt
:source {
Test formula which needs AB-mixed interpolators
Desired Interpolant: (and (<= y x1) (implies (>= y x1) (< (f (- x1 5)) x2)))
}
:status unsat
:difficulty { 0 }
:logic AUFLIRA
:extrafuns ((a1 Real))
:extrafuns ((a2 Real))
:extrafuns ((b1 Real))
:extrafuns ((b2 Real))
:extrafuns ((x1 Real))
:extrafuns ((x2 Real))
:extrafuns ((y Real))
:extrafuns ((f Real Real))
:assumption
(and (<= (* 5.0 a1) x1) (and (= (f a1) a2) (and (<= y a1) (< a2 x2))))
:formula
(and (<= x1 (* 5.0 b1)) (and (= (f b1) b2) (and (<= b1 y) (< x2 b2)))))
