;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)

(set-info :status unsat)

(set-logic QF_ABV)

(declare-fun myArray () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun k () (_ BitVec 8))

(assert (= (select myArray (_ bv0 8)) (_ bv42 8)))
(assert (= k (_ bv1 8)))
(assert (not (= (select myArray (bvadd k (_ bv255 8))) (_ bv42 8))))

(check-sat)

(exit)
