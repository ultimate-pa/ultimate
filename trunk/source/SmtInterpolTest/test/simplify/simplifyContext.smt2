(set-logic QF_UFLIRA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (> a 0))
(simplify (=> (or (< a 0) (> b 0)) (ite (> b 0) (> c 0) (< c 0))))
;RESULT: (=> (> b 0) (> c 0))

