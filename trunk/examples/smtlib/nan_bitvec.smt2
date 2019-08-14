(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-logic ALL)


; (assert (= ((_ extract 31 31) b) (_ bv0 1)))

(echo "Analyse 32 Bitvec NaNs.")
(echo "[signbit 31]")
(echo "")

(push 1)
(declare-fun b () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(declare-fun n () (_ FloatingPoint 8 24))
(assert (= (_ NaN 8 24) n))
(assert (= ((_ to_fp 8 24) b) n))
(assert (= ((_ to_fp 8 24) d) n))

(push 1)
(echo "zero vector:")
(assert (= b
;        7       5       3       1
; 01234567890123456789012345678901
#b00000000000000000000000000000000))
(check-sat)
(pop 1)
(push 1)

(echo "one vector:")
(assert (= b
;        7       5       3       1
; 01234567890123456789012345678901
#b11111111111111111111111111111111))
(check-sat)
(pop 1)


(push 1)
(echo "7-0 zero")
(assert (= ((_ extract 7 0) b) #b00000000))
(check-sat)
(pop 1)


(push 1)
(echo "15-8 zero")
(assert (= ((_ extract 15 8) b) #b00000000))
(check-sat)
(pop 1)


(push 1)
(echo "23-16 zero")
(assert (= ((_ extract 23 16) b) #b00000000))
(check-sat)
(pop 1)


(push 1)
(echo "31-24 zero")
(assert (= ((_ extract 31 24) b) #b00000000))
(check-sat)
(pop 1)

(echo "")


(push 1)
(echo "22-0 zero")
(assert (= ((_ extract 22 0) b) #b00000000000000000000000))
(check-sat)
(pop 1)
(push 1)
(echo "22-0 zero, except a single 1")
(assert (= ((_ extract 22 0) b) #b00000000001000000000000))
(check-sat)
(pop 1)
(push 1)
(echo "signbit")
(assert (= ((_ extract 31 31) b) #b0))
(assert (= ((_ extract 31 31) d) #b1))
(check-sat)
(pop 1)


(echo "==> NaNs must follow the following scheme:")
(echo "0-22 != only 0s")
(echo "23-30 = only 1s")
(echo "31 = signbit either 0 or 1") 
(pop 1)

(push 1)
(echo "")
(echo "Different BitVectors to_fp => equal to NaN")
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun f () (_ FloatingPoint 8 24))
(declare-fun g () (_ FloatingPoint 8 24))
(assert (= (_ NaN 8 24) f))
(assert (= (_ NaN 8 24) g))
(assert (= ((_ to_fp 8 24) a) f))
(assert (= ((_ to_fp 8 24) b) g))
(assert (= ((_ extract 16 16) a) #b0))
(assert (= ((_ extract 16 16) b) #b1))
(check-sat)
(pop 1)
