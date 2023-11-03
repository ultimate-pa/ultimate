(= x 0)
(= i 0)
(= j 0)
(= i j)

(>= x y)

(= i (+ j 1))
(= j (+ i 1))
(>= x (+ y (select A j)))
(>= (+ x (select A i)) y)

(>= i N)
(>= j N)
(< i N)
(< j N)
