(set-info :source "{
This contains the tree-interpolants for the McCarthy example from the paper

 M. Heizmann, J. Hoenicke, A. Podelski, Nested Interpolants, POPL 2010

The first query computes the nested interpolants for Figure 6/7.
Desired Interpolants:
   x_1    <= 100,
   xm1    <= 111,
     true,
     res4 <= x2 - 10,
   resm5  <= 101,
   xm6    <= 101,
     x7   >= 101,
     res8 >= 91 && res8 <= x7 - 10,
   resm10 == 91
   res11  == 91 

The second query computes the interpolants for Figure 4 (right).
Desired Interpolants (cf. Figure 9):
   true,
   true,
   x2    >= 101,
   x2    >= 101 && res4 = x2 - 10,

}")
(set-info :status unsat)
(set-info :difficulty "{ 0 }")
(set-option :produce-proofs true)
(set-logic QF_LIA)
(push 1)
(declare-fun x_1 () Int)
(declare-fun xm1 () Int)
(declare-fun x2 () Int)
(declare-fun res4 () Int)
(declare-fun resm5 () Int)
(declare-fun xm6 () Int)
(declare-fun x7 () Int)
(declare-fun res9 () Int)
(declare-fun resm10 () Int)
(declare-fun res11 () Int)
(assert (! (<= x_1 100) :named M1))
(assert (! (= xm1 (+ x_1 11)) :named M2))
(assert (! (> x2 100) :named S11))
(assert (! (= res4 (- x2 10)) :named S12))
(assert (! (and (= x2 xm1) (= resm5 res4)) :named S1RET))
(assert (! (= xm6 resm5) :named M3))
(assert (! (> x7 100) :named S21))
(assert (! (= res9 (- x7 10)) :named S22))
(assert (! (and (= x7 xm6) (= resm10 res9)) :named S2RET))
(assert (! (= res11 resm10) :named M4))
(assert (! (and (<= x_1 101) (distinct res11 91)) :named ERR))
(check-sat)
(get-interpolants M1 M2 (S11 S12) S1RET M3 (S21 S22) S2RET M4 ERR)
(pop 1)
; Interpolants for Figure 4 and Figure 9
(push 1)
(declare-fun x_1 () Int)
(declare-fun xm1 () Int)
(declare-fun x2 () Int)
(declare-fun res4 () Int)
(assert (! (<= x_1 100) :named M1))
(assert (! (= xm1 (+ x_1 11)) :named M2))
(assert (! (= x2 xm1) :named CALL))
(assert (! (> x2 100) :named S1))
(assert (! (= res4 (- x2 10)) :named S2))
(assert (! (and (<= x2 101) (distinct res4 91)) :named ERR))
(check-sat)
(get-interpolants M1 M2 CALL S1 S2 ERR)
;Actual Interpolants:
;Interpolant 0: true
;Interpolant 1: true
;Interpolant 2: true
;Interpolant 3: (<= 0 (+ x2 (- 101)))
;Interpolant 4: (and (<= 0 (+ res4 (- 91))) (<= res4 (+ x2 (- 10))))
(pop 1)
(exit)
