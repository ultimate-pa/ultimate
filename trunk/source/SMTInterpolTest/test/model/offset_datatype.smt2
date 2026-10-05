; Model construction with an offset equality inside a datatype constructor:
; the numeric field of (mk (+ y 5) 0) must keep its +5 offset in the model, so
; (fst p) evaluates to y + 5 = 8 rather than y = 3.
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-info :status sat)
(set-logic QF_UFDTLIA)
(declare-datatype Pair ((mk (fst Int) (snd Int))))
(declare-fun p () Pair)
(declare-fun y () Int)
(assert (= p (mk (+ y 5) 0)))
(assert (= y 3))
(check-sat)
(get-model)
