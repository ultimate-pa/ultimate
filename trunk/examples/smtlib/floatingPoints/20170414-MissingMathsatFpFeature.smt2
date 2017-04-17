; 20170414 heizmann@informatik.uni-freiburg.de
; I sent this script to Alberto because output of MathSAT5 version 5.4.0 is
; the following
;  (error "ERROR: fp argument 1 must be a bit-vector number (y given)")
;
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-logic QF_FPBV)
(set-info :source |
    SMT that describes feature needed by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.5)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ BitVec 1))
(assert (! (= (fp y (_ bv0 8) (_ bv0 23)) x) :named ssa_1_conjunct1))
(check-sat)
