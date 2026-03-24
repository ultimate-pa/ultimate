(set-logic QF_ABV)

(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const c (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const d (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const e (Array (_ BitVec 1) (_ BitVec 1)))

(assert (distinct a b c d e))
(check-sat)
