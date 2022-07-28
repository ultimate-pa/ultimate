(set-option :print-success true)

(set-logic HORN)

(set-info :source |SMT script generated on 2022-07-27T17:43:27+02:00 by Ultimate (https://ultimate.informatik.uni-freiburg.de/)|)

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

(declare-fun isLoad (Action Variable) Bool)

(declare-fun isStore (Action Variable) Bool)

(declare-fun a () Action)

(declare-fun b () Action)

(assert (=> (dominates a b) (notReachableFrom a b) (mustHappenBefore a b)))

(assert (forall ((b Action) (a Action)) (=> (thCreates a b) (mustHappenBefore a b))))

(assert (forall ((b Action) (a Action)) (=> (thJoins a b) (mustHappenBefore b a))))

(assert (forall ((b Action) (c Action) (a Action)) (=> (mustHappenBefore a b) (mustHappenBefore b c) (mustHappenBefore a c))))

(assert (forall ((x Variable) (s1 Action) (s2 Action) (l Action)) (let ((.cse0 (isStore l x))) (=> (readsFrom l s1) (mustHappenBefore s1 s2) (isLoad l x) .cse0 .cse0))))

(assert (forall ((b Action) (a Action)) (=> (mustHappenBefore a b) (readsFrom a b) false)))

(assert (forall ((l2 Action) (l1 Action) (x Variable) (s1 Action) (s2 Action)) (=> (and (readsFrom l1 s1) (mustHappenBefore l1 s2) (mustHappenBefore s2 l2) (isLoad l1 x) (isLoad l2 x) (isStore s1 x) (isStore s2 x) (readsFrom l2 s1)) false)))

(declare-fun action0 () Action)

(declare-fun action1 () Action)

(assert (notReachableFrom action0 action1))

(declare-fun action2 () Action)

(assert (notReachableFrom action2 action0))

(assert (notReachableFrom action2 action1))

(declare-fun action3 () Action)

(assert (notReachableFrom action3 action0))

(assert (notReachableFrom action3 action2))

(declare-fun action4 () Action)

(assert (notReachableFrom action3 action4))

(assert (notReachableFrom action3 action1))

(declare-fun action5 () Action)

(assert (notReachableFrom action5 action0))

(assert (notReachableFrom action5 action2))

(assert (notReachableFrom action5 action3))

(assert (notReachableFrom action5 action4))

(assert (notReachableFrom action5 action1))

(declare-fun action6 () Action)

(declare-fun action7 () Action)

(assert (notReachableFrom action6 action7))

(declare-fun action8 () Action)

(assert (notReachableFrom action6 action8))

(declare-fun action9 () Action)

(assert (notReachableFrom action6 action9))

(declare-fun action10 () Action)

(assert (notReachableFrom action6 action10))

(declare-fun action11 () Action)

(declare-fun action12 () Action)

(assert (notReachableFrom action11 action12))

(declare-fun action13 () Action)

(assert (notReachableFrom action11 action13))

(declare-fun action14 () Action)

(assert (notReachableFrom action11 action14))

(declare-fun action15 () Action)

(assert (notReachableFrom action11 action15))

(assert (notReachableFrom action13 action11))

(assert (notReachableFrom action13 action12))

(assert (notReachableFrom action14 action11))

(assert (notReachableFrom action14 action12))

(assert (notReachableFrom action14 action13))

(assert (notReachableFrom action15 action11))

(assert (notReachableFrom action15 action12))

(assert (notReachableFrom action15 action13))

(assert (notReachableFrom action15 action14))

(declare-fun action16 () Action)

(declare-fun action17 () Action)

(assert (notReachableFrom action16 action17))

(assert (notReachableFrom action16 action11))

(assert (notReachableFrom action16 action12))

(assert (notReachableFrom action16 action13))

(assert (notReachableFrom action16 action14))

(declare-fun action18 () Action)

(assert (notReachableFrom action16 action18))

(assert (notReachableFrom action16 action15))

(declare-fun action19 () Action)

(assert (notReachableFrom action16 action19))

(declare-fun action20 () Action)

(assert (notReachableFrom action20 action16))

(declare-fun action21 () Action)

(assert (notReachableFrom action20 action21))

(assert (notReachableFrom action20 action17))

(assert (notReachableFrom action20 action11))

(assert (notReachableFrom action20 action12))

(assert (notReachableFrom action20 action13))

(assert (notReachableFrom action20 action14))

(declare-fun action22 () Action)

(assert (notReachableFrom action20 action22))

(assert (notReachableFrom action20 action18))

(assert (notReachableFrom action20 action15))

(declare-fun action23 () Action)

(assert (notReachableFrom action20 action23))

(assert (notReachableFrom action20 action19))

(assert (notReachableFrom action21 action16))

(assert (notReachableFrom action21 action20))

(assert (notReachableFrom action21 action17))

(assert (notReachableFrom action21 action11))

(assert (notReachableFrom action21 action12))

(assert (notReachableFrom action21 action13))

(assert (notReachableFrom action21 action14))

(assert (notReachableFrom action21 action18))

(assert (notReachableFrom action21 action15))

(assert (notReachableFrom action21 action19))

(assert (notReachableFrom action17 action16))

(assert (notReachableFrom action17 action20))

(assert (notReachableFrom action17 action21))

(assert (notReachableFrom action17 action11))

(assert (notReachableFrom action17 action12))

(assert (notReachableFrom action17 action13))

(assert (notReachableFrom action17 action14))

(assert (notReachableFrom action17 action18))

(assert (notReachableFrom action17 action15))

(assert (notReachableFrom action17 action19))

(assert (notReachableFrom action22 action16))

(assert (notReachableFrom action22 action20))

(assert (notReachableFrom action22 action21))

(assert (notReachableFrom action22 action17))

(assert (notReachableFrom action22 action11))

(assert (notReachableFrom action22 action12))

(assert (notReachableFrom action22 action13))

(assert (notReachableFrom action22 action14))

(assert (notReachableFrom action22 action18))

(assert (notReachableFrom action22 action15))

(assert (notReachableFrom action22 action23))

(assert (notReachableFrom action22 action19))

(declare-fun action24 () Action)

(declare-fun action25 () Action)

(assert (notReachableFrom action24 action25))

(declare-fun action26 () Action)

(assert (notReachableFrom action26 action25))

(assert (notReachableFrom action26 action24))

(declare-fun action27 () Action)

(assert (notReachableFrom action27 action25))

(assert (notReachableFrom action27 action24))

(assert (notReachableFrom action27 action26))

(declare-fun action28 () Action)

(assert (notReachableFrom action28 action25))

(assert (notReachableFrom action28 action24))

(assert (notReachableFrom action28 action26))

(assert (notReachableFrom action28 action27))

(declare-fun action29 () Action)

(assert (notReachableFrom action29 action25))

(assert (notReachableFrom action29 action24))

(assert (notReachableFrom action29 action26))

(assert (notReachableFrom action29 action27))

(assert (notReachableFrom action29 action28))

(declare-fun action30 () Action)

(assert (notReachableFrom action30 action25))

(assert (notReachableFrom action30 action24))

(assert (notReachableFrom action30 action26))

(assert (notReachableFrom action30 action27))

(assert (notReachableFrom action30 action28))

(assert (notReachableFrom action30 action29))

(declare-fun action31 () Action)

(assert (notReachableFrom action31 action30))

(assert (notReachableFrom action31 action25))

(assert (notReachableFrom action31 action24))

(assert (notReachableFrom action31 action26))

(assert (notReachableFrom action31 action27))

(assert (notReachableFrom action31 action28))

(assert (notReachableFrom action31 action29))

(declare-fun action32 () Action)

(assert (notReachableFrom action32 action30))

(assert (notReachableFrom action32 action31))

(assert (notReachableFrom action32 action25))

(assert (notReachableFrom action32 action24))

(assert (notReachableFrom action32 action26))

(assert (notReachableFrom action32 action27))

(assert (notReachableFrom action32 action28))

(assert (notReachableFrom action32 action29))

(assert (notReachableFrom action7 action6))

(assert (notReachableFrom action7 action8))

(assert (notReachableFrom action7 action9))

(assert (notReachableFrom action7 action10))

(assert (notReachableFrom action18 action11))

(assert (notReachableFrom action18 action12))

(assert (notReachableFrom action18 action13))

(assert (notReachableFrom action18 action14))

(assert (notReachableFrom action18 action15))

(assert (notReachableFrom action23 action16))

(assert (notReachableFrom action23 action20))

(assert (notReachableFrom action23 action21))

(assert (notReachableFrom action23 action17))

(assert (notReachableFrom action23 action11))

(assert (notReachableFrom action23 action12))

(assert (notReachableFrom action23 action13))

(assert (notReachableFrom action23 action14))

(assert (notReachableFrom action23 action18))

(assert (notReachableFrom action23 action15))

(assert (notReachableFrom action23 action19))

(assert (notReachableFrom action4 action0))

(assert (notReachableFrom action4 action2))

(assert (notReachableFrom action4 action1))

(assert (notReachableFrom action19 action11))

(assert (notReachableFrom action19 action12))

(assert (notReachableFrom action19 action13))

(assert (notReachableFrom action19 action14))

(assert (notReachableFrom action19 action18))

(assert (notReachableFrom action19 action15))

(assert (thCreates action30 action12))

(assert (thCreates action31 action12))

(assert (thCreates action28 action1))

(assert (thCreates action29 action7))

(assert (thCreates action29 action10))

(declare-fun var0 () Variable)

(assert (isLoad action16 var0))

(declare-fun var1 () Variable)

(assert (isLoad action20 var1))

(declare-fun var2 () Variable)

(assert (isLoad action20 var2))

(assert (isLoad action21 var1))

(assert (isLoad action21 var2))

(assert (isLoad action17 var0))

(assert (isLoad action6 var1))

(assert (isLoad action6 var2))

(assert (isLoad action9 var1))

(assert (isLoad action9 var2))

(declare-fun var3 () Variable)

(assert (isLoad action12 var3))

(assert (isLoad action18 var3))

(assert (isLoad action23 var3))

(assert (isLoad action4 var3))

(assert (isLoad action8 var3))

(assert (isLoad action19 var3))

(assert (isLoad action1 var3))

(assert (isLoad action10 var3))

(assert (isStore action0 var2))

(assert (isStore action2 var1))

(assert (isStore action3 var0))

(assert (isStore action25 var2))

(assert (isStore action24 var1))

(assert (isStore action26 var0))

(assert (isStore action27 var3))

(assert (isStore action12 var3))

(assert (isStore action13 var2))

(assert (isStore action14 var1))

(assert (isStore action18 var3))

(assert (isStore action15 var0))

(assert (isStore action23 var3))

(assert (isStore action4 var3))

(assert (isStore action8 var3))

(assert (isStore action19 var3))

(assert (isStore action1 var3))

(assert (isStore action10 var3))

