(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-option :print-terms-cse false)

(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_remove.spl:49:4-14:This deallocation might be unsafe
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_28$0 () Bool)
(declare-fun Axiom_29$0 () Bool)
(declare-fun Axiom_30$0 () Bool)
(declare-fun Axiom_31$0 () Bool)
(declare-fun Axiom_32$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun c_2$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun d_2$0 () Loc)
(declare-fun d_3$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prev_1$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_46$0 () SetLoc)
(declare-fun sk_?X_47$0 () SetLoc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)
(declare-fun sk_?X_52$0 () SetLoc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y)
            (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y)
            (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next_1$0 prv_2$0 (read$0 next_1$0 prv_2$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_3$0) prv_3$0))
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next_1$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P9))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P10))

(assert (! (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) (read$0 next$0 prv_3$0)) :named P11))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P12))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P13))

(assert (! (Btwn$0 next_1$0 prv_2$0 (read$0 next_1$0 prv_2$0) (read$0 next_1$0 prv_2$0)) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_50$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y sk_?X_50$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_50$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y sk_?X_50$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_50$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_50$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_50$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y sk_?X_50$0)))) :named P18))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_50$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_50$0)))) :named P19))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_50$0 c_1$0)
  (ep$0 next$0 sk_?X_50$0 c_1$0)) :named P20))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_50$0 d_1$0)
  (ep$0 next$0 sk_?X_50$0 d_1$0)) :named P21))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_50$0 curr_3$0)
  (ep$0 next$0 sk_?X_50$0 curr_3$0)) :named P22))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_50$0 prv_2$0)
  (ep$0 next$0 sk_?X_50$0 prv_2$0)) :named P23))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_50$0 prv_3$0)
  (ep$0 next$0 sk_?X_50$0 prv_3$0)) :named P24))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_51$0)) (not (in$0 c_1$0 sk_?X_51$0)))) :named P25))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_51$0)) (not (in$0 c_1$0 sk_?X_51$0)))) :named P26))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_51$0)) (not (in$0 c_1$0 sk_?X_51$0)))) :named P27))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_51$0)) (not (in$0 c_1$0 sk_?X_51$0)))) :named P28))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_51$0)) (not (in$0 curr_3$0 sk_?X_51$0)))) :named P29))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_51$0)) (not (in$0 curr_3$0 sk_?X_51$0)))) :named P30))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_51$0)) (not (in$0 curr_3$0 sk_?X_51$0)))) :named P31))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_51$0)) (not (in$0 curr_3$0 sk_?X_51$0)))) :named P32))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 tmp_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) tmp_2$0)) (not (in$0 d_1$0 sk_?X_51$0))
        (not (in$0 tmp_2$0 sk_?X_51$0)))) :named P33))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) tmp_2$0))
        (not (in$0 prv_3$0 sk_?X_51$0)) (not (in$0 tmp_2$0 sk_?X_51$0)))) :named P34))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) tmp_2$0))
        (not (in$0 prv_2$0 sk_?X_51$0)) (not (in$0 tmp_2$0 sk_?X_51$0)))) :named P35))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 tmp_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) tmp_2$0))
        (not (in$0 curr_3$0 sk_?X_51$0)) (not (in$0 tmp_2$0 sk_?X_51$0)))) :named P36))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_51$0))
        (not (in$0 prv_2$0 sk_?X_51$0)))) :named P37))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_51$0)) (not (in$0 prv_2$0 sk_?X_51$0)))) :named P38))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_51$0)) (not (in$0 prv_2$0 sk_?X_51$0)))) :named P39))

(assert (! (or (not Axiom_31$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_51$0)) (not (in$0 prv_2$0 sk_?X_51$0)))) :named P40))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_53$0)) (not (in$0 c_1$0 sk_?X_53$0)))) :named P41))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_53$0)) (not (in$0 c_1$0 sk_?X_53$0)))) :named P42))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_53$0)) (not (in$0 c_1$0 sk_?X_53$0)))) :named P43))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_53$0)) (not (in$0 c_1$0 sk_?X_53$0)))) :named P44))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_53$0)) (not (in$0 curr_3$0 sk_?X_53$0)))) :named P45))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_53$0)) (not (in$0 curr_3$0 sk_?X_53$0)))) :named P46))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_53$0)) (not (in$0 curr_3$0 sk_?X_53$0)))) :named P47))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_53$0)) (not (in$0 curr_3$0 sk_?X_53$0)))) :named P48))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 tmp_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) tmp_2$0)) (not (in$0 d_1$0 sk_?X_53$0))
        (not (in$0 tmp_2$0 sk_?X_53$0)))) :named P49))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) tmp_2$0))
        (not (in$0 prv_3$0 sk_?X_53$0)) (not (in$0 tmp_2$0 sk_?X_53$0)))) :named P50))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) tmp_2$0))
        (not (in$0 prv_2$0 sk_?X_53$0)) (not (in$0 tmp_2$0 sk_?X_53$0)))) :named P51))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 tmp_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) tmp_2$0))
        (not (in$0 curr_3$0 sk_?X_53$0)) (not (in$0 tmp_2$0 sk_?X_53$0)))) :named P52))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_53$0))
        (not (in$0 prv_2$0 sk_?X_53$0)))) :named P53))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_53$0)) (not (in$0 prv_2$0 sk_?X_53$0)))) :named P54))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_53$0)) (not (in$0 prv_2$0 sk_?X_53$0)))) :named P55))

(assert (! (or (not Axiom_29$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_53$0)) (not (in$0 prv_2$0 sk_?X_53$0)))) :named P56))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_50$0 c_1$0) sk_?X_50$0)
    (= c_1$0 (ep$0 next$0 sk_?X_50$0 c_1$0))) :named P57))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_50$0 d_1$0) sk_?X_50$0)
    (= d_1$0 (ep$0 next$0 sk_?X_50$0 d_1$0))) :named P58))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_50$0 curr_3$0) sk_?X_50$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_50$0 curr_3$0))) :named P59))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_50$0 prv_2$0) sk_?X_50$0)
    (= prv_2$0 (ep$0 next$0 sk_?X_50$0 prv_2$0))) :named P60))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_50$0 prv_3$0) sk_?X_50$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_50$0 prv_3$0))) :named P61))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P62))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P63))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P64))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P65))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P66))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P67))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P68))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P69))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 tmp_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) tmp_2$0)) (not (in$0 d_1$0 sk_?X_48$0))
        (not (in$0 tmp_2$0 sk_?X_48$0)))) :named P70))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) tmp_2$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 tmp_2$0 sk_?X_48$0)))) :named P71))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) tmp_2$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 tmp_2$0 sk_?X_48$0)))) :named P72))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 tmp_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) tmp_2$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 tmp_2$0 sk_?X_48$0)))) :named P73))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_48$0))
        (not (in$0 prv_2$0 sk_?X_48$0)))) :named P74))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P75))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P76))

(assert (! (or (not Axiom_32$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P77))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P78))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P79))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P80))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P81))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P82))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P83))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P84))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P85))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 tmp_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) tmp_2$0)) (not (in$0 d_1$0 sk_?X_46$0))
        (not (in$0 tmp_2$0 sk_?X_46$0)))) :named P86))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) tmp_2$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 tmp_2$0 sk_?X_46$0)))) :named P87))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) tmp_2$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 tmp_2$0 sk_?X_46$0)))) :named P88))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 tmp_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) tmp_2$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 tmp_2$0 sk_?X_46$0)))) :named P89))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_46$0))
        (not (in$0 prv_2$0 sk_?X_46$0)))) :named P90))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P91))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P92))

(assert (! (or (not Axiom_30$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P93))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_54$0)) (not (in$0 c_1$0 sk_?X_54$0)))) :named P94))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_54$0)) (not (in$0 c_1$0 sk_?X_54$0)))) :named P95))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_54$0)) (not (in$0 c_1$0 sk_?X_54$0)))) :named P96))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_54$0)) (not (in$0 c_1$0 sk_?X_54$0)))) :named P97))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_54$0)) (not (in$0 curr_3$0 sk_?X_54$0)))) :named P98))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_54$0)) (not (in$0 curr_3$0 sk_?X_54$0)))) :named P99))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_54$0)) (not (in$0 curr_3$0 sk_?X_54$0)))) :named P100))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_54$0)) (not (in$0 curr_3$0 sk_?X_54$0)))) :named P101))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 tmp_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) tmp_2$0)) (not (in$0 d_1$0 sk_?X_54$0))
        (not (in$0 tmp_2$0 sk_?X_54$0)))) :named P102))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) tmp_2$0))
        (not (in$0 prv_3$0 sk_?X_54$0)) (not (in$0 tmp_2$0 sk_?X_54$0)))) :named P103))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 tmp_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) tmp_2$0))
        (not (in$0 prv_2$0 sk_?X_54$0)) (not (in$0 tmp_2$0 sk_?X_54$0)))) :named P104))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 tmp_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) tmp_2$0))
        (not (in$0 curr_3$0 sk_?X_54$0)) (not (in$0 tmp_2$0 sk_?X_54$0)))) :named P105))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_54$0))
        (not (in$0 prv_2$0 sk_?X_54$0)))) :named P106))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_54$0)) (not (in$0 prv_2$0 sk_?X_54$0)))) :named P107))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_54$0)) (not (in$0 prv_2$0 sk_?X_54$0)))) :named P108))

(assert (! (or (not Axiom_28$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_54$0)) (not (in$0 prv_2$0 sk_?X_54$0)))) :named P109))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P110))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P111))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_50$0 FP$0))
                 (or (in$0 x sk_?X_50$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_50$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_50$0 FP$0)))))) :named P112))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_49$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_49$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_49$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_49$0)))))) :named P113))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P114))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_46$0 sk_?X_48$0))
                 (or (in$0 x sk_?X_46$0) (in$0 x sk_?X_48$0)))
            (and (not (in$0 x sk_?X_46$0)) (not (in$0 x sk_?X_48$0))
                 (not (in$0 x (union$0 sk_?X_46$0 sk_?X_48$0)))))) :named P115))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_1$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_1$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P116))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_53$0 FP$0))
                 (or (in$0 x sk_?X_53$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_53$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_53$0 FP$0)))))) :named P117))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_53$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_53$0 FP$0)))
            (and (or (not (in$0 x sk_?X_53$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_53$0 FP$0)))))) :named P118))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_46$0) (in$0 x sk_?X_48$0)
                 (in$0 x (intersection$0 sk_?X_46$0 sk_?X_48$0)))
            (and (or (not (in$0 x sk_?X_46$0)) (not (in$0 x sk_?X_48$0)))
                 (not (in$0 x (intersection$0 sk_?X_46$0 sk_?X_48$0)))))) :named P119))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_50$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_50$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_50$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_50$0)))))) :named P120))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P121))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_50$0))
                 (not (in$0 x sk_?X_50$0)))
            (and (or (in$0 x sk_?X_50$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_50$0)))))) :named P122))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P123))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P124))

(assert (! (= (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_3$0) tmp_2$0) :named P125))

(assert (! (or (= d_1$0 prv_3$0)
    (= (read$0 next$0 d_1$0) (read$0 (write$0 next$0 prv_3$0 tmp_2$0) d_1$0))) :named P126))

(assert (! (or (= prv_3$0 prv_3$0)
    (= (read$0 next$0 prv_3$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_3$0))) :named P127))

(assert (! (or (= prv_2$0 prv_3$0)
    (= (read$0 next$0 prv_2$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_2$0))) :named P128))

(assert (! (or (= curr_3$0 prv_3$0)
    (= (read$0 next$0 curr_3$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) curr_3$0))) :named P129))

(assert (! (= (read$0 (write$0 prev$0 tmp_2$0 prv_3$0) tmp_2$0) prv_3$0) :named P130))

(assert (! (or (= c_1$0 tmp_2$0)
    (= (read$0 prev$0 c_1$0) (read$0 (write$0 prev$0 tmp_2$0 prv_3$0) c_1$0))) :named P131))

(assert (! (or (= curr_3$0 tmp_2$0)
    (= (read$0 prev$0 curr_3$0)
      (read$0 (write$0 prev$0 tmp_2$0 prv_3$0) curr_3$0))) :named P132))

(assert (! (or (= tmp_2$0 tmp_2$0)
    (= (read$0 prev$0 tmp_2$0)
      (read$0 (write$0 prev$0 tmp_2$0 prv_3$0) tmp_2$0))) :named P133))

(assert (! (or (= prv_2$0 tmp_2$0)
    (= (read$0 prev$0 prv_2$0)
      (read$0 (write$0 prev$0 tmp_2$0 prv_3$0) prv_2$0))) :named P134))

(assert (! (= (read$0 next$0 null$0) null$0) :named P135))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P136))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P137))

(assert (! (= (read$0 prev_1$0 null$0) null$0) :named P138))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P139))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P140))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_53$0)))
         Axiom_29$0)
    (not
         (dlseg_struct$0 sk_?X_53$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P141))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_51$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_31$0)
    (not
         (dlseg_struct$0 sk_?X_51$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P142))

(assert (! (or
    (and (= c_2$0 c_3$0) (= c_3$0 tmp_2$0) (= next_1$0 next$0)
         (= prv_3$0 null$0))
    (and (= next_1$0 (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)))
         (not (= prv_3$0 null$0)))) :named P143))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P144))

(assert (! (= c_1$0 a$0) :named P145))

(assert (! (= curr_2$0 c_1$0) :named P146))

(assert (! (= d_2$0 d_1$0) :named P147))

(assert (! (= tmp_2$0 (read$0 next$0 curr_3$0)) :named P148))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P149))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P150))

(assert (! (= emptyset$0 (intersection$0 sk_?X_47$0 sk_?X_48$0)) :named P151))

(assert (! (= sk_?X_47$0 sk_?X_46$0) :named P152))

(assert (! (= sk_?X_49$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P153))

(assert (! (dlseg_struct$0 sk_?X_46$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P154))

(assert (! (not (= curr_3$0 null$0)) :named P155))

(assert (! (= emptyset$0 (intersection$0 sk_?X_52$0 sk_?X_51$0)) :named P156))

(assert (! (= sk_?X_50$0 FP_1$0) :named P157))

(assert (! (= sk_?X_52$0 sk_?X_53$0) :named P158))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P159))

(assert (! (dlseg_struct$0 sk_?X_53$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P160))

(assert (! (= sk_?X_54$0 FP$0) :named P161))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P162))

(assert (! (not (= a$0 null$0)) :named P163))

(assert (! (not (in$0 null$0 Alloc$0)) :named P164))

(assert (! (not (in$0 curr_3$0 FP_2$0)) :named P165))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_1$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                     prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 c_1$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                          prv_2$0)))))) :named P166))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                     d_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          d_1$0)))))) :named P167))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_54$0)))
         Axiom_28$0)
    (not (dlseg_struct$0 sk_?X_54$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P168))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_46$0)))
         Axiom_30$0)
    (not
         (dlseg_struct$0 sk_?X_46$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P169))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_48$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_32$0)
    (not
         (dlseg_struct$0 sk_?X_48$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P170))

(assert (! (or
    (and (= d_2$0 d_3$0) (= d_3$0 prv_3$0) (= prev_1$0 prev$0)
         (= tmp_2$0 null$0))
    (and (= prev_1$0 (write$0 prev$0 tmp_2$0 prv_3$0))
         (not (= tmp_2$0 null$0)))) :named P171))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P172))

(assert (! (= c_2$0 c_1$0) :named P173))

(assert (! (= d_1$0 b$0) :named P174))

(assert (! (= prv_2$0 null$0) :named P175))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P176))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P177))

(assert (! (= emptyset$0 emptyset$0) :named P178))

(assert (! (= sk_?X_46$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P179))

(assert (! (= sk_?X_48$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P180))

(assert (! (= sk_?X_49$0 (union$0 sk_?X_47$0 sk_?X_48$0)) :named P181))

(assert (! (dlseg_struct$0 sk_?X_48$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P182))

(assert (! (= emptyset$0 emptyset$0) :named P183))

(assert (! (= sk_?X_50$0 (union$0 sk_?X_52$0 sk_?X_51$0)) :named P184))

(assert (! (= sk_?X_51$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P185))

(assert (! (= sk_?X_53$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P186))

(assert (! (dlseg_struct$0 sk_?X_51$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P187))

(assert (! (not (= curr_2$0 null$0)) :named P188))

(assert (! (= sk_?X_54$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P189))

(assert (! (dlseg_struct$0 sk_?X_54$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P190))

(assert (! (not (= a$0 b$0)) :named P191))

(assert (! (not (in$0 null$0 Alloc$0)) :named P192))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P193))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_2$0 l1 curr_3$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                     prv_3$0))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 c_2$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                          prv_3$0)))))) :named P194))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                     d_2$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                          d_2$0)))))) :named P195))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0 (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)) ?z
                   ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v prv_3$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z prv_3$0
                                               prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u prv_3$0)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v
                                     prv_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 curr_3$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 curr_3$0)
                                               prv_3$0 prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?u ?v)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v
                                     prv_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 curr_3$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 curr_3$0)
                                               prv_3$0 prv_3$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v prv_3$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u prv_3$0)
                      (or (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v prv_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 curr_3$0)
                                      prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?u ?v)
                      (or (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v prv_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 curr_3$0)
                                      prv_3$0 prv_3$0)))))
                 (not
                      (Btwn$0
                        (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)) ?z
                        ?u ?v))))) :named P196))

(assert (! (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)) :named P197))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P198))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))) :named P199))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P200))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))) :named P201))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P202))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))) :named P203))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P204))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))) :named P205))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P206))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))) :named P207))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P208))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))) :named P209))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P210))

(check-sat)

(get-interpolants (and P140 P167 P107 P0 P136 P11 P77 P52 P84 P6 P210 P26 P189 P102 P39 P20 P105 P201 P65 P126 P1 P188 P74 P171 P122 P186 P61 P116 P133 P193 P23 P56 P68 P131 P45 P158 P183 P185 P156 P54 P197 P33 P30 P16 P97 P99 P48 P181 P137 P159 P96 P47 P141 P55 P209 P195 P168 P206 P100 P70 P152 P93 P4 P19 P166 P135 P87 P64 P13 P46 P163 P132 P120 P129 P7 P89 P104 P184 P60 P138 P69 P106 P194 P98 P155 P151 P110 P148 P143 P180 P41 P101 P153 P146 P8 P165 P34 P95 P78 P128 P44 P82 P161 P187 P172 P90) (and P127 P51 P35 P196 P203 P150 P59 P67 P2 P86 P49 P24 P176 P38 P85 P76 P103 P81 P14 P25 P21 P124 P40 P145 P190 P162 P73 P147 P119 P83 P75 P3 P198 P121 P199 P92 P134 P72 P113 P22 P142 P169 P62 P31 P94 P144 P42 P43 P80 P37 P58 P164 P71 P29 P109 P191 P179 P17 P91 P149 P63 P192 P36 P182 P114 P200 P27 P9 P32 P28 P118 P125 P66 P123 P160 P202 P157 P117 P204 P53 P177 P173 P79 P57 P130 P205 P112 P88 P10 P108 P15 P178 P111 P175 P208 P115 P174 P12 P207 P170 P5 P139 P154 P50 P18))

(exit)