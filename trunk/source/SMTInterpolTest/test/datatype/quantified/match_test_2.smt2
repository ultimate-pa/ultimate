(set-info :smt-lib-version 2.6)
(set-logic UFDTLIA)

(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "random")
(set-info :status sat)


;integer lists  with "nil" and "cons" constructors
(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car Int) (cdr List) ))))

(declare-fun append (List List) List)


;should be false, because not every constructor of List is in one of the patterns and no pattern is a variable
(assert (
forall  
((l1 List) (l2 List))
(= 

(append  l1 l2)
(match l1 ((nil l2)))

)
))
