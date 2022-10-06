(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ( (List 0) (Tree 0) ) (
 ( (nil) (cons (car U) (cdr List) ))
 ( (leaf (data U)) (node (left Tree) (right Tree)) )
))

(declare-const d Tree)
(declare-fun p0 (U) Bool)
(declare-fun p1 (Tree Tree) Bool)

(assert (not (= (match d (((leaf x) (p0 x)) ((node x y) (p1 x y))))
                (ite ((_ is leaf) d) (p0 (data d)) (p1 (left d) (right d))))))

(check-sat)
(get-proof)
