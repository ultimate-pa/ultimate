(set-logic HORN)
(set-info :status sat)

; Args: c (program variable), m (mutex), l (loc counter for l1) location (0/1)
(declare-fun I (Bool Bool Int Int) Bool)

; Safe
(assert (forall ((c Bool) (m Bool) (l Int)) (=> (I c m l 1) c)))

; Initial
(assert (forall ((c Bool) (m Bool) (l Int)) (=> (= l 0) (I c m l 0))))

; Inductive
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (I c m l 0) (not m) m1 c1) (I c1 m1 (+ l 1) 1))))
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (I c m l 1) m (not m1) (not c1)) (I c1 m1 (- l 1) 0))))

; Non-interference
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (>= l 0) (I c m l 0) (not m) m1 c1) (I c1 m1 (+ l 1) 0))))
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (>= l 1) (I c m l 1) (I c m l 0) (not m) m1 c1) (I c1 m1 (+ l 1) 1))))
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (>= l 1) (I c m l 0) (I c m l 1) m (not m1) (not c1)) (I c1 m1 (- l 1) 0))))
(assert (forall ((c Bool) (m Bool) (c1 Bool) (m1 Bool) (l Int)) (=> (and (>= l 2) (I c m l 1) m (not m1) (not c1)) (I c1 m1 (- l 1) 1))))

(check-sat)
(get-model)