(benchmark pidgeonhole10.smt
:source {

}
:status unsat
:difficulty { 1 }
:logic QF_LIA
:extrafuns ((i1 Int) (i2 Int) (i3 Int) (i4 Int) (i5 Int) (i6 Int) (i7 Int) (i8
Int))
:assumption
(distinct i1 i2 i3 i4 i5 i6 i7 i8)
:formula
(and
  (<= 1 i1) (<= i1 7)
  (<= 1 i2) (<= i2 7)
  (<= 1 i3) (<= i3 7)
  (<= 1 i4) (<= i4 7)
  (<= 1 i5) (<= i5 7)
  (<= 1 i6) (<= i6 7)
  (<= 1 i7) (<= i7 7)
  (<= 1 i8) (<= i8 7)
)
)
