(set-info :smt-lib-version 2.6)
(set-logic UFDTLIA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "random")
(set-info :status sat)


(declare-datatypes ((|(Nat)| 0) (List 1) (|Tree| 2))
  (((succ (pred |(Nat)|)) (zero))
   (par (X) ((|;cons| (car X) (cdr (List X))) (null)))
   (par (X Y) ((node (key X) (children (List (Tree X Y)))) (leaf (data Y))))
  ))

(declare-fun append ((List |(Nat)|) (List |(Nat)|)) (List |(Nat)|))


(assert (forall ((l1 (List |(Nat)|)) (l2 (List |(Nat)|)))
	(= (append  l1 l2)
	   (match l1 ((null l2) ((|;cons| h t) (|;cons| h (append t l2)))))
	)
))
