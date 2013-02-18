(benchmark groundtest1.smt
:source {
}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrafuns ((P Int Int) (Q Int Int Int))
:extrafuns ((foo1 Int) (foo2 Int) (bar Int))
:notes "Interpolation Problem starts here"
:assumption
(forall (?x Int) (iff (= (P ?x) 0) (forall (?y Int) (= (Q ?x ?y) 0) :pat { (Q ?x ?y) })) :pat { (P ?x) })
:assumption
(forall (?y Int) (= (Q foo2 ?y) 0) :pat { (Q foo2 ?y) } )
:formula
(or (not (= (P foo2) 0)) (and (= (P foo1) 0) (not (= (Q foo1 bar) 0))))
)
