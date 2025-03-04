# Make a case distinction over whether n is positive or not.
# If any loop is completely skipped, we have n <= 0 and all loops must be skipped.
# Only if n is positive, things get interesting.
(<= n 0)
(> n 0)

# Possible values for x in traces that obey loop bounds.
(= x 0)
(= x 1)
(= x (- 1))
(= x 2)

# It remains only to show that the loop bounds must match.
# We begin with the initializations of counters.
(= i 0)
(= j 0)

# If thread1 enters its loop, we have i<n and the invariant is i<=n (in case n is positive).
(< i n)
(<= i n)

# While thread1 is in the first loop, the reduction should have i==j as invariant.
(= i j)
(= i (+ j 1))

# While thread1 is in the second loop, the reduction should have n+2i==j as invariant.
(= (+ n (* 2 i)) j)
(= (+ n (* 2 i)) (+ j 1))
(= (+ n (* 2 i)) (+ j 2))

# When thread1 exits the first loop, we have i=n and due to i==j also j=n.
(= i n)
(= j n)

# When thread2 exits its loop, we have j>=3n.
(>= j (* 3 n))

