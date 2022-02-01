(benchmark groundtest2_inst.smt
:source {
}
:status unsat
:difficulty { 0 }
:logic AUFLIA
:extrapreds ((P Int) (Q Int Int))
:extrafuns ((foo1 Int) (foo2 Int) (bar Int))
:extrafuns ((x1 Int) (x2 Int) (y1 Int) (y_sk Int) (x3 Int) (y3 Int))
:notes "Interpolation Problem starts here"
:assumption
(and (implies (P x1) (Q x1 y1))
     (implies (Q x1 y_sk) (P x1))
     (implies (P x2) (Q x2 y1))
     (implies (Q x2 y_sk) (P x2))
     (= y3 y_sk))
:assumption
(and (Q x3 y3))
:formula
(and
     (= x1 foo1)
     (= x2 foo2)
     (= x3 foo2)
     (= y1 bar)
(or (not (P foo2)) (and (P foo1) (not (Q foo1 bar))))
)
)
