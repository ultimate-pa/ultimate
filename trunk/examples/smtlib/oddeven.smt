(benchmark evenodd.smt
:source {
UNKNOWN - But this is a typical cut example
}
:status unsat
:difficulty { 0 }
:logic QF_LIA
:extrafuns ((x Int))
:extrafuns ((y Int))
:extrafuns ((z Int))
:assumption
(= x (+ (* 2 z) 1))
:formula
(= x (* 2 y)))
