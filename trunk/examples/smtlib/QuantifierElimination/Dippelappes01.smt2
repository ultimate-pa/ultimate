(set-info :smt-lib-version 2.6)
(set-option :produce-unsat-cores true)
(set-logic ALIA)
(set-info :source |
Example that tests our support for unsat cores.
Since the formula 'potato' is on the assertion stack, the quantifier 
elimination replaces the formula 'leek' by false. We detect that 'potato' 
supported the quantifier elimination and add it to the unsatisfiable core.
2019-06-21, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "craftet")
(set-info :status unsat)
(declare-fun k1 () Int)
(declare-fun k2 () Int)
(assert (! (= k1 23) :named bacon))
(assert (! (= k1 k2) :named potato))
(assert (! (exists ((a (Array Int Int))) (not (= (select a k1) (select a k2)))) :named leek))
(check-sat)
(get-unsat-core)
(exit)
