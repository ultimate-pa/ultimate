(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) (Tree 1) ) (
 ( (nil) (cons (car U) (cdr List) ))
 (par (X) ( (leaf (data U)) (node (left (Tree X)) (right (Tree X))) (leaf1) (leaf2) (leaf3) ))
))

(declare-const d (Tree U))
(declare-fun p0 (U) U)
(declare-fun p1 ((Tree U) (Tree U)) U)
(declare-fun p2 ((Tree U)) U)
(declare-fun p3 () U)

(assert (not (= (match d ((leaf2 p3)
                          (x (p0 (p2 x)))
                          ((leaf x) (p0 x))
                          ((leaf x) (p0 (p0 x)))
			  (x (p2 x))))
                (ite ((_ is leaf2) d) p3 (p0 (p2 d))))))

(check-sat)
(get-proof)
