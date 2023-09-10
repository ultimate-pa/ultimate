(set-logic HORN)
(set-info :status sat)

; Args: m, l1, l2
(declare-fun I (Int Int Int) Bool)

; Symmetry
(assert (forall ((m Int) (l1 Int) (l2 Int)) (=> (I m l1 l2) (I m l2 l1))))

; Safe
(assert (forall ((m Int) (l2 Int)) (=> (I m 1 l2) (= m 1))))

; Initial
(assert (forall ((value Int) (m Int) (v1 Int) (v2 Int)) (=> (= m 0) (I m 0 0))))

; Inductive
(assert (forall ((m Int) (l2 Int) (pm Int)) (=> (and (I m 0 l2) (= m 0) (= pm 1)) (I pm 1 l2))))
(assert (forall ((m Int) (l2 Int) (pm Int)) (=> (and (I m 1 l2) (= pm 0)) (I pm 2 l2))))

; Non-interference
(assert (forall ((m Int) (l1 Int) (l2 Int) (pm Int)) (=> (and (I m l1 l2) (I m 0 l2) (I m l1 0) (= m 0) (= pm 1)) (I pm l1 l2))))
(assert (forall ((m Int) (l1 Int) (l2 Int) (pm Int)) (=> (and (I m l1 l2) (I m 1 l2) (I m l1 1) (= pm 0)) (I pm l1 l2))))

(check-sat)
(get-model)