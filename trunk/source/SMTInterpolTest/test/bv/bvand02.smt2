(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))

(assert (= (bvand a #x0f0f99cc) #x06081004))
(assert (= (bvand #xf0f06633 a) #x50700230))
(check-sat)
(get-model)

(assert (not (= a #x56781234)))
(check-sat)
(set-option :print-terms-cse false)
(get-proof)
