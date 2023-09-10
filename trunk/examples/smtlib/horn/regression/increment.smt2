(set-logic HORN)
(set-info :status sat)

; Args: value, m, l1, v1, l2, v2
(declare-fun I (Int Int Int Int Int Int) Bool)

; Symmetry
;(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int) (l2 Int)) (=> (I value m l1 v1 l2 v2) (I value m l2 v2 l1 v1))))

; Safe
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l2 Int)) (=> (I value m 2 v1 l2 v2) (> value v1))))
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int)) (=> (I value m l1 v1 2 v2) (> value v2))))

; Initial
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int)) (=> (= m 0) (I value m 0 v1 0 v2))))

; Inductive
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l2 Int) (pm Int) (pv1 Int))
(=> (and (I value m 0 v1 l2 v2) (= pv1 value) (= m 0) (= pm 1)) (I value pm 1 pv1 l2 v2))))
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int) (pm Int) (pv2 Int))
(=> (and (I value m l1 v1 0 v2) (= pv2 value) (= m 0) (= pm 1)) (I value pm l1 v1 1 pv2))))

(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l2 Int) (pm Int) (pvalue Int))
(=> (and (I value m 1 v1 l2 v2) (= pvalue (+ v1 1)) (= m 1) (= pm 0)) (I pvalue pm 2 v1 l2 v2))))
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int) (pm Int) (pvalue Int))
(=> (and (I value m l1 v1 1 v2) (= pvalue (+ v2 1)) (= m 1) (= pm 0)) (I pvalue pm l1 v1 2 v2))))

; Non-interference
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int) (l2 Int) (pm Int) (pvalue Int) (v Int))
(=> (and (I value m l1 v1 l2 v2) (I value m 1 v l2 v2) (I value m l1 v1 1 v) (= pvalue (+ v 1)) (= m 1) (= pm 0)) (I pvalue pm l1 v1 l2 v2))))

(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int) (l1 Int) (l2 Int) (pm Int) (pv Int))
(=> (and (I value m l1 v1 l2 v2) (I value m 0 v1 l2 v2) (I value m l1 v1 0 v2) (= pv value) (= m 0) (= pm 1)) (I value pm l1 v1 l2 v2))))

(check-sat)
(get-model)