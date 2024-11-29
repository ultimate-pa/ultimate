(set-logic QF_BV)

(assert (bvugt (_ bv255 8) (_ bv128 8) (_ bv5 8) (_ bv0 8)))
(assert (bvuge (_ bv255 8) (_ bv255 8) (_ bv128 8) (_ bv5 8) (_ bv0 8)))
(assert (bvult (_ bv0 8) (_ bv2 8) (_ bv128 8) (_ bv255 8)))
(assert (bvule (_ bv0 8) (_ bv2 8) (_ bv128 8) (_ bv128 8) (_ bv255 8)))
(assert (bvsgt (_ bv5 8) (_ bv0 8) (_ bv255 8) (_ bv128 8)))
(assert (bvsge (_ bv5 8) (_ bv0 8) (_ bv255 8) (_ bv255 8) (_ bv128 8)))
(assert (bvslt (_ bv128 8) (_ bv255 8) (_ bv0 8) (_ bv2 8)))
(assert (bvsle (_ bv128 8) (_ bv128 8) (_ bv255 8) (_ bv0 8) (_ bv2 8)))
(check-sat)

