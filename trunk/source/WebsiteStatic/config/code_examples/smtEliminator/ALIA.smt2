(set-info :smt-lib-version 2.6)
(set-logic ALIA)
(declare-fun k () Int)
(declare-fun i () Int)
(declare-fun v () Int)
(declare-fun b () (Array Int Int))
; select over store, exists
(simplify (exists ((ax (Array Int Bool))) (not (select (store (store ax k true) i true) v))))
; select over store, forall
(simplify (forall ((ax (Array Int Int))) (or (not (= (select (store ax k v) i) 7)) (= i k))))
; negated equality of arrays
(simplify (exists ((ax (Array Int Int))) (and (not (= ax b)) (= (store b k v) ax))))
(declare-fun kOuter () Int)
(declare-fun iOuter () Int)
(declare-fun kInner () Int)
(declare-fun iInner () Int)
; multi-dimensional arrays
(simplify (forall ((ax (Array Int (Array Int Int)))) (or (not (= (select (select (store ax kOuter (store (select ax kOuter) kInner v)) iOuter) iInner) 7)) (not (= iOuter kOuter)))))
