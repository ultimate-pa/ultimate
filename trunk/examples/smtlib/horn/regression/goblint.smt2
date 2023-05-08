(set-logic HORN)
(set-info :status sat)

; g m l1 l2
(declare-fun I (Int Int Int Int) Bool)

; Symmetry
(assert (forall ((g Int) (m Int) (l1 Int) (l2 Int)) (=> (I g m l1 l2) (I g m l2 l1))))

; Safe
(assert (forall ((g Int) (m Int) (loc Int)) (=> (I g m 3 loc) (= g 0))))

; Initial
(assert (forall ((g Int) (m Int)) (=> (= g 0) (I g m 0 0))))

; Inductive
(assert (forall ((g Int) (m Int) (m2 Int) (loc Int)) (=> (I g m 0 loc) (= m 0) (= m2 1) (I g m2 1 loc))))
(assert (forall ((g Int) (g2 Int) (m Int) (loc Int)) (=> (I g m 1 loc) (= g2 (+ g 1)) (I g2 m 2 loc))))
(assert (forall ((g Int) (g2 Int) (m Int) (loc Int)) (=> (I g m 2 loc) (= g2 (- g 1)) (I g2 m 3 loc))))
(assert (forall ((g Int) (m Int) (m2 Int) (loc Int)) (=> (I g m 3 loc) (= m 1) (= m2 0) (I g m2 4 loc))))

; Non-interference
(assert (forall ((g Int) (m Int) (m2 Int) (l1 Int) (l2 Int)) (=> (I g m l1 l2) (I g m 0 l2) (I g m l1 0) (= m 0) (= m2 1)(I g m2 l1 l2))))
(assert (forall ((g Int) (g2 Int) (m Int) (l1 Int) (l2 Int)) (=> (I g m l1 l2) (I g m 1 l2) (I g m l1 1) (= g2 (+ g 1)) (I g2 m l1 l2))))
(assert (forall ((g Int) (g2 Int) (m Int) (l1 Int) (l2 Int)) (=> (I g m l1 l2) (I g m 2 l2) (I g m l1 2) (= g2 (- g 1)) (I g2 m l1 l2))))
(assert (forall ((g Int) (m Int) (m2 Int) (l1 Int) (l2 Int)) (=> (I g m l1 l2) (I g m 3 l2) (I g m l1 3) (= m 1) (= m2 0)(I g m2 l1 l2))))

(check-sat)
(get-model)