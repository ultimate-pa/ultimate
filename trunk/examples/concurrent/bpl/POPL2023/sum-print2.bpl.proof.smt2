(= x 0)
(= i 0)
(= k 0)
(= i k)

(= x y)

(= i (+ k 1))
(= k (+ i 1))
(= x (+ y (select A k)))
(= x (+ y (select A k) (select A (+ k 1))))
(= (+ x (select A i)) y)

(>= i N)
(>= k N)
(< i N)
(< k N)
