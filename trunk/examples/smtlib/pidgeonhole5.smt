(benchmark pidgeonhole10.smt
:source {

}
:status sat
:difficulty { 0 }
:logic QF_LIA
:extrafuns ((i1 Int) (i2 Int) (i3 Int) (i4 Int) (i5 Int))
:assumption
(distinct i1 i2 i3 i4 i5)
:formula
(and
  (<= 1 i1) (<= i1 4)
  (<= 1 i2) (<= i2 4)
  (<= 1 i3) (<= i3 4)
  (<= 1 i4) (<= i4 4)
  (<= 1 i5) (<= i5 4)
)
)
