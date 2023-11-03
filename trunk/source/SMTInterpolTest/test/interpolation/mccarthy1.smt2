(set-option :produce-interpolants true)
(set-info :source |
This is the example in Figure 6 of the paper

 M. Heizmann, J. Hoenicke, A. Podelski, Nested Interpolants, POPL 2010

This computes the interpolants omitting the two calls.

Desired Interpolants (see Figure 7):
   x_1 <= 100,
   xm1 <= 111,
   
   true,
   res4 <= x2 - 10,

   resm5 <= 101
   xm6 <= 101

   x7 >= 101,
   x7 >= 101 && res <= x7 - 10

   resm10 == 91
   res11  == 91 

Actual Interpolants:

   (<= x_1 100)
   (<= xm1 111)

   true
   (<= res4 (+ x2 (- 10)))

   (<= resm5 101)
   (<= xm6 101) 

   (<= 0 (+ x7 (- 101)))
   (and (<= res9 (+ x7 (- 10))) (<= 0 (+ res9 (- 91))))
  
   (and (<= resm10 91) (<= 0 (+ resm10 (- 91))))
   (let ((.cse0 (+ res11 (- 91)))) 
     (ite (not (<= (+ res11 (- 90)) 0))
          (=> (not (<= .cse0 0)) (<= res11 91))
          (<= 0 .cse0)))

The last formula is equivalent to res11 == 91.

|)
(set-info :status unsat)
(set-logic QF_UFLIA)
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
(assert (! (<= x_1 100) :named IP_0))
(assert (! (= xm1 (+ x_1 11)) :named IP_1))
(assert (! (= x2 xm1) :named IP_2))
(assert (! (> x2 100) :named IP_3))
(assert (! (= res4 (- x2 10)) :named IP_4))
(assert (! (= resm5 res4) :named IP_5))
(assert (! (= xm6 resm5) :named IP_6))
(assert (! (= x7 xm6) :named IP_7))
(assert (! (> x7 100) :named IP_8))
(assert (! (= res9 (- x7 10)) :named IP_9))
(assert (! (= resm10 res9) :named IP_10))
(assert (! (= res11 resm10) :named IP_11))
(assert (! (and (<= x_1 101) (distinct res11 91)) :named IP_12))
(check-sat)
(get-interpolants IP_0 IP_1 (IP_3 IP_4) (and IP_2 IP_5) IP_6 
                  (IP_8 IP_9) (and IP_7 IP_10) IP_11 IP_12)
(exit)
