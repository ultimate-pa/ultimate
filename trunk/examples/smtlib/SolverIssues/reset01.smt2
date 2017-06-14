; Date: 2017-06-13
; Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
(reset)
(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-logic ALL)
(set-info :source |
    SMT script generated on 2017/06/14 by Ultimate. http://ultimate.informatik.uni-freiburg.de/
|)
(set-info :smt-lib-version 2.5)
(set-info :category "industrial")
(assert true)
(reset)
(set-option :print-success true)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-logic ALL)
;
; Response of MathSAT 5.4.1 is
; (error "set-logic is invalid at this point")
;
; However, according to Figure 4.1 of Section 4.1 of [SMT-LIB 2.5](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.5-r2015-06-28.pdf)
; the reset command brings the solver back to the "Start mode".
