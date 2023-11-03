(set-logic HORN)
(set-info :status sat)

; Args: l1, l2, c, m
(declare-fun I (Int Int Int Int) Bool)

; Symmetry
;(assert (forall ((c Int) (m Int) (l1 Int) (l2 Int)) (=> (I l1 l2 c m) (I l2 l1 c m))))

; Safe
(assert (forall ((c Int) (m Int) (l2 Int)) (=> (I 2 l2 c m) (= c 1))))
(assert (forall ((c Int) (m Int) (l2 Int)) (=> (I l2 2 c m) (= c 1))))

; Initial
(assert (I 0 0 0 0))

; Inductive
(assert (forall ((c Int) (m Int) (m2 Int) (l2 Int)) (=> (I 0 l2 c m) (= m 0) (= m2 1) (I 1 l2 c m2))))
(assert (forall ((c Int) (m Int) (m2 Int) (l2 Int)) (=> (I l2 0 c m) (= m 0) (= m2 1) (I l2 1 c m2))))

(assert (forall ((c Int) (m Int) (c2 Int) (l2 Int)) (=> (I 1 l2 c m) (= c2 (+ c 1)) (I 2 l2 c2 m))))
(assert (forall ((c Int) (m Int) (c2 Int) (l2 Int)) (=> (I l2 1 c m) (= c2 (+ c 1)) (I l2 2 c2 m))))

(assert (forall ((c Int) (m Int) (c2 Int) (l2 Int)) (=> (I 2 l2 c m) (= c2 (- c 1)) (I 3 l2 c2 m))))
(assert (forall ((c Int) (m Int) (c2 Int) (l2 Int)) (=> (I l2 2 c m) (= c2 (- c 1)) (I l2 3 c2 m))))

(assert (forall ((c Int) (m Int) (m2 Int) (l2 Int)) (=> (I 3 l2 c m) (= m2 0) (I 0 l2 c m2))))
(assert (forall ((c Int) (m Int) (m2 Int) (l2 Int)) (=> (I l2 3 c m) (= m2 0) (I l2 0 c m2))))

; Non-interference
(assert (forall ((l1 Int) (l2 Int) (c Int) (m Int) (m2 Int)) (=> (I l1 l2 c m) (I 0 l2 c m) (I l1 0 c m) (= m 0) (= m2 1) (I l1 l2 c m2))))
(assert (forall ((l1 Int) (l2 Int) (c Int) (m Int) (c2 Int)) (=> (I l1 l2 c m) (I 1 l2 c m) (I l1 1 c m) (= c2 (+ c 1)) (I l1 l2 c2 m))))
(assert (forall ((l1 Int) (l2 Int) (c Int) (m Int) (c2 Int)) (=> (I l1 l2 c m) (I 2 l2 c m) (I l1 2 c m) (= c2 (- c 1)) (I l1 l2 c2 m))))
(assert (forall ((l1 Int) (l2 Int) (c Int) (m Int) (m2 Int)) (=> (I l1 l2 c m) (I 3 l2 c m) (I l1 3 c m) (= m2 0) (I l1 l2 c m2))))

(check-sat)
(get-model)