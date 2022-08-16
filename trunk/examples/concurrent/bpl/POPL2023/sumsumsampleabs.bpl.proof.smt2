# proof is sufficient with variable-based abstraction & syntactic commutativity
# (presuming quantifier elimination in the abstraction is turned on)

# assertions to prove loop-lockstep interleavings of threads sum1 and sum2
# ------------------------------------------------------------------------

(= sum1 0)
(= i1 0)
(= sum1 sum2)
(= i1 i2)
(= sum1 (+ sum2 (let ((x (select A i2))) (ite (< x 0) (- x) x))))
(= i1 (+ i2 1))


# index inequalities needed to prove that both loops run same number of iterations
# --------------------------------------------------------------------------------

(>= i1 N)
(>= i2 N)
(< i1 N)
(< i2 N)

