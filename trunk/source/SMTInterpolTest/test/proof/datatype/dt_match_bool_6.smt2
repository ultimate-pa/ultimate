(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) (Tree 0) ) (
 ( (nil) (cons (car U) (cdr List) ))
 ( (leaf (data U)) (node (left Tree) (right Tree)) (leaf1) (leaf2) (leaf3) )
))

(declare-const d Tree)
(declare-fun p0 (U) Bool)
(declare-fun p1 (Tree Tree) Bool)
(declare-fun p2 (Tree) Bool)
(declare-fun p3 () Bool)

(assert (not (= (match d ((leaf2 p3)
                          (x (not (p2 x)))
                          ((leaf x) (p0 x))
                          ((leaf x) (not (p0 x)))
			  (x (p2 x))))
                (ite ((_ is leaf2) d) p3 (not (p2 d))))))

(check-sat)
(get-proof)
