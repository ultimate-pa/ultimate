(set-info :smt-lib-version 2.6)
(set-logic UFDTLIA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "random")
(set-info :status sat)


;integer lists  with "nil" and "cons" constructors
(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car Int) (cdr List) ))))

(declare-fun append (List List) List)


(assert (
forall  
((l1 List) (l2 List))
(= 

;should be true, because one of the patterns is a variable
(append  l1 l2)
(match l1 ( (nil l2) (l2 l2) ) )

)
))
