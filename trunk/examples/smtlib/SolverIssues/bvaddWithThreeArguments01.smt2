; Date: 2017-06-14
; Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
(set-logic QF_BV)
(set-info :source |
    SMT script generated on 2017/06/14 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.5)
(set-info :category "industrial")

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (! (= (bvadd x y (_ bv1 32)) (_ bv23 32)) :named ssa_1_conjunct0))
(check-sat)
;
; Response of MathSAT 5.4.1 is
; (error "ERROR: bvadd takes exactly 2 arguments (3 given) (line: 10)")
;
; The MathSAT response is consistent with the SMT-LIB standard:
; * bvadd is defined for two arguments in the [bitvector theory](http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)
; * and in contrast to the plus operator of the [integer theory](http://smtlib.cs.uiowa.edu/theories-Ints.shtml)
;   bvadd is not marked as :left-assoc
;
; However, Ultimate uses all bitvector functions that are indeed 
; left-associative with an arbitrary number of arguments.
