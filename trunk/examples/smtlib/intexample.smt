(benchmark ddmexample.smt
:source {
A Fast Linear-Arithmetic Solver for DPLL(T) by Bruno Dutertre and Leonardo de 
Moura
}
:status unsat
:difficulty { 0 }
:logic AUFLIRA
:extrafuns ((x Int))
:extrafuns ((y Int))
:assumption
(<= 1 (- (* 3 x) (* 3 y)))
:formula
(<= (- (* 3 x) (* 3 y)) 2))
