# Make a case distinction over whether n is positive or not.
# If any loop is completely skipped, we have n <= 0 and all loops must be skipped.
# Only if n is positive, things get interesting.
(<= n 0)
(> n 0)

# Possible values for x in traces that obey loop bounds.
(= x 0)
(= x (- c))
(= x c)
(= x (* 2 c))
(= x (* 3 c))

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
(= (+ i 1) j)

# While thread1 is in the second loop, we have n+2i==j as invariant.
(= (+ n (* 2 i)) j)
(= (+ n (* 2 i) 1) j)
(= (+ n (* 2 i)) (+ j 1))

# While thread1 is in the third loop, the reduction should have 2n+3i==j as invariant.
(= (+ (* 2 n) (* 3 i)) j)
(= (+ (* 2 n) (* 3 i) 1) j)
(= (+ (* 2 n) (* 3 i)) (+ j 1))

# When thread1 exits the first loop, we have i=n and due to i==j also j=n.
(= i n)
(= j n)

# When thread1 exits the second loop, we have i=2n and j=3n
(= i (* 2 n))
(= j (* 3 n))

# When thread1 exits the third loop, we have i=3n and j=6n
(= i (* 3 n))
(= j (* 6 n))

# When thread2 exits its loop, we have j>=6n.
(>= j (* 6 n))

