(set-option :print-success false)
(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 8))

(push 1)
(assert (= a #x0000ffff))
(check-sat)
(get-model)

(assert (not (= a (_ bv65535 32))))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (= b #b00010110))
(check-sat)
(get-model)

(assert (not (= b (_ bv22 8))))
(check-sat)
(get-proof)
(pop 1)
