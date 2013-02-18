(benchmark pidgeonhole10.smt
:source {

}
:status unsat
:difficulty { 2 }
:logic QF_LIA
:extrafuns ((i1 Int) (i2 Int) (i3 Int) (i4 Int) (i5 Int) (i6 Int) (i7 Int) (i8
Int) (i9 Int) (i10 Int))
:assumption
(distinct i1 i2 i3 i4 i5 i6 i7 i8 i9 i10)
:formula
(and
  (<= 1 i1) (<= i1 9)
  (<= 1 i2) (<= i2 9)
  (<= 1 i3) (<= i3 9)
  (<= 1 i4) (<= i4 9)
  (<= 1 i5) (<= i5 9)
  (<= 1 i6) (<= i6 9)
  (<= 1 i7) (<= i7 9)
  (<= 1 i8) (<= i8 9)
  (<= 1 i9) (<= i9 9)
  (<= 1 i10) (<= i10 9))
)
