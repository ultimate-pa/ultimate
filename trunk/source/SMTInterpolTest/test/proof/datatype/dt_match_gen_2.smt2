(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) (Tree 1) ) (
 ( (nil) (cons (car U) (cdr List) ))
 (par (X) ( (leaf (data U)) (node (left (Tree X)) (right (Tree X))) ))
))

(declare-const d (Tree U))
(declare-fun p0 (U) U)
(declare-fun p1 ((Tree U) (Tree U)) U)

(assert (not (= (match d (((leaf x) (p0 x))
                          ((node x y) (p1 x y))
                          ((leaf x) (p0 (p0 x)))))
                (ite ((_ is leaf) d) (p0 (data d)) (p1 (left d) (right d))))))

(check-sat)
(get-proof)
