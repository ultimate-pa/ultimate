(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))

(assert (= (bvand a #x0000ffff) #x00001234))
(assert (= (bvand (bvsub (_ bv0 32) (_ bv65536 32)) a) #x56780000))
(check-sat)
(get-model)

(assert (not (= a #x56781234)))
(check-sat)
(set-option :print-terms-cse false)
(get-proof)
