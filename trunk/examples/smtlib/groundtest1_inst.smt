(benchmark groundtest1_inst.smt
:source {
}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrapreds ((P Int) (Q Int Int))
:extrafuns ((foo1 Int) (foo2 Int) (bar Int) (sky Int))
:extrafuns ((x1 Int) (x2 Int) (y1 Int) (y2 Int))
:assumption
(and (= y2 sky)
     (implies (P x2) (Q x2 y1))
     (implies (P x1) (Q x1 y1))
     (implies (Q x2 sky) (P x2))
     (implies (Q x1 sky) (P x1)))
:assumption
(and (Q foo2 y2))
:formula
(and
(= x1 foo1)
(= x2 foo2)
(= y1 bar)
(or (not (P foo2)) (and (P foo1) (not (Q foo1 bar))))
)
)
