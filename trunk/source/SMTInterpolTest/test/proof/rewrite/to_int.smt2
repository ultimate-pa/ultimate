(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_LIRA)

(push 1)
(assert (not (= (to_int (/ 123456 3224)) 38)))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (not (= (to_int (/ 125735 3224)) 38)))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (not (= (to_int (/ 125736 3224)) 39)))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (not (= (to_int (/ (- 125736) 3224)) (- 39))))
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (not (= (to_int (/ (- 125737) 3224)) (- 40))))
(check-sat)
(get-proof)
(pop 1)

