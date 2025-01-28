# Make a case distinction over whether n is positive or not.
# If any loop is completely skipped, we have n <= 0 and all loops must be skipped.
# Only if n is positive, things get interesting.
(<= n 0)
(> n 0)

# Possible values for x in traces that obey loop bounds.
(= x 0)
(= x c)
(= x (* 2 c))

# It remains only to show that the loop bounds must match.
# We begin with the initializations of counters.
(= i 0)
(= j 0)

# We always have i < n and j < n
(< i n)
(< (+ i 1) n)
(<= i n)
(< j n)
(< (+ j 1) n)
(<= j n)

# Ideally we want i == j as an invariant.
(= i j)
(= i (+ j 1))
(= (+ i 1) j)

# When both threads are done, we have i=n and due to i==j also j=n.
(= i n)
(= j n)
