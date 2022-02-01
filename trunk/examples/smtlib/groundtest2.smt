(benchmark groundtest2.smt
:source {
}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrapreds ((P Int) (Q Int Int))
:extrafuns ((foo1 Int) (foo2 Int) (bar Int))
:notes "Interpolation Problem starts here"
:assumption
(forall (?x Int) (iff (P ?x) (forall (?y Int) (Q ?x ?y) :pat { (Q ?x ?y) })) :pat { (P ?x) })
:assumption
(forall (?y Int) (Q foo2 ?y) :pat { (Q foo2 ?y) } )
:formula
(or (not (P foo2)) (and (P foo1) (not (Q foo1 bar))))
)
