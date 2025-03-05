# Make a case distinction over whether n is positive or not.
# If any loop is completely skipped, we have n <= 0 and all loops must be skipped.
# Only if n is positive, things get interesting.
(<= n 0)
(> n 0)

# Possible values for x in traces that obey loop bounds.
(= x (* 2 (- c)))
(= x (- c))
(= x 0)
(= x c)
(= x (* 2 c))

# It remains only to show that the loop bounds must match.
# We begin with the initializations of counters.
(= i 0)
(= j 0)
(= k 0)

# Loop Bounds
(< i n)
(<= i n)
(< j (* 2 n))
(<= j (* 2 n))
(< k (* 4 n))
(<= k (* 4 n))

# Index invariants of the first lockstep order
(= k (* 2 i))
(= k (- (* 2 i) 1))
(= k (- (* 2 i) 2))
(= k (* 2 n))
(= k (* 4 n))
(= j (* 2 n))

# Index invariants of the second lockstep order
(= k (+ (* 2 n) j))
(= k (+ (* 2 n) (+ j 1)))
(= k (+ (* 2 n) (- j 1)))

