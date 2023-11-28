(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)

(set-info :smt-lib-version 2.6)
(set-logic QF_UFDTLIA)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) ) (
 ( (nil) (cons (car Int) (cdr List) ))
))

(declare-const a Int)
(declare-const b Int)
(declare-const z Int)
(declare-const u List)
(declare-const v List)
(declare-const w List)
(declare-const t List)

;; injective

(assert (! (= (cons a u) w) :named A ))
(assert (! (= (cons (+ a 1) v) w) :named B )) 
(assert (! (= a b) :named C ))

(check-sat)
(get-interpolants A B C)
(get-interpolants C A B)
(get-interpolants B C A)
(get-interpolants C B A)
(get-interpolants A C B)
(get-interpolants B A C)
(exit)
