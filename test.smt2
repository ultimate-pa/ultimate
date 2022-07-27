(set-option :print-success true)

(set-logic HORN)

(set-info :source |SMT script generated on 2022-07-22T12:40:50+02:00 by Ultimate (https://ultimate.informatik.uni-freiburg.de/)|)

(set-info :smt-lib-version 2.5)

(set-info :category "industrial")

(set-info :ultimate-id HornClauseSolver)

(declare-sort Action 0)

(declare-sort Variable 0)

(declare-fun dominates (Action Action) Bool)

(declare-fun notReachableFrom (Action Action) Bool)

(declare-fun mustHappenBefore (Action Action) Bool)

(declare-fun thCreates (Action Action) Bool)

(declare-fun thJoins (Action Action) Bool)

(declare-fun readsFrom (Action Action) Bool)

