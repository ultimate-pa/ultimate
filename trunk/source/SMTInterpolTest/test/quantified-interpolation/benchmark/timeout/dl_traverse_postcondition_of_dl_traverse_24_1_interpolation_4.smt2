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
  tests/spl/dl/dl_traverse.spl:24:1-2:A postcondition of procedure dl_traverse might not hold at this return point
  tests/spl/dl/dl_traverse.spl:13:10-32:Related location: This is the postcondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
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
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun Axiom_5$0 () Bool)
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun a_1$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun b_1$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_l1_1$0 () Loc)
(declare-fun sk_l2_1$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b$0 ?y ?y)) (= b$0 ?y)
            (Btwn$0 next$0 b$0 (read$0 next$0 b$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 a_1$0 ?y ?y)) (= a_1$0 ?y)
            (Btwn$0 next$0 a_1$0 (read$0 next$0 a_1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y)
            (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_l1_1$0 ?y ?y)) (= sk_l1_1$0 ?y)
            (Btwn$0 next$0 sk_l1_1$0 (read$0 next$0 sk_l1_1$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b$0) b$0)) (not (Btwn$0 next$0 b$0 ?y ?y))
            (= b$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 a_1$0) a_1$0))
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (= a_1$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_3$0) prv_3$0))
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_l1_1$0) sk_l1_1$0))
            (not (Btwn$0 next$0 sk_l1_1$0 ?y ?y)) (= sk_l1_1$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P9))

(assert (! (Btwn$0 next$0 b$0 (read$0 next$0 b$0) (read$0 next$0 b$0)) :named P10))

(assert (! (Btwn$0 next$0 a_1$0 (read$0 next$0 a_1$0) (read$0 next$0 a_1$0)) :named P11))

(assert (! (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) (read$0 next$0 prv_3$0)) :named P12))

(assert (! (Btwn$0 next$0 sk_l1_1$0 (read$0 next$0 sk_l1_1$0) (read$0 next$0 sk_l1_1$0)) :named P13))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P14))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 b$0) sk_?X_7$0)
    (= b$0 (ep$0 next$0 sk_?X_7$0 b$0))) :named P15))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 lst_1$0) sk_?X_7$0)
    (= lst_1$0 (ep$0 next$0 sk_?X_7$0 lst_1$0))) :named P16))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 curr_3$0) sk_?X_7$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_7$0 curr_3$0))) :named P17))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 a_1$0) sk_?X_7$0)
    (= a_1$0 (ep$0 next$0 sk_?X_7$0 a_1$0))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 prv_3$0) sk_?X_7$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_7$0 prv_3$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 sk_l1_1$0) sk_?X_7$0)
    (= sk_l1_1$0 (ep$0 next$0 sk_?X_7$0 sk_l1_1$0))) :named P20))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_7$0 sk_l2_1$0) sk_?X_7$0)
    (= sk_l2_1$0 (ep$0 next$0 sk_?X_7$0 sk_l2_1$0))) :named P21))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_4$0)) (not (in$0 lst_1$0 sk_?X_4$0)))) :named P22))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_4$0))
        (not (in$0 lst_1$0 sk_?X_4$0)))) :named P23))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_4$0)) (not (in$0 lst_1$0 sk_?X_4$0)))) :named P24))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_4$0)) (not (in$0 lst_1$0 sk_?X_4$0)))) :named P25))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_4$0)) (not (in$0 lst_1$0 sk_?X_4$0)))) :named P26))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_4$0))
        (not (in$0 sk_l2_1$0 sk_?X_4$0)))) :named P27))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_4$0)) (not (in$0 sk_l2_1$0 sk_?X_4$0)))) :named P28))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_4$0)) (not (in$0 sk_l2_1$0 sk_?X_4$0)))) :named P29))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_4$0)) (not (in$0 sk_l2_1$0 sk_?X_4$0)))) :named P30))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_4$0)) (not (in$0 sk_l2_1$0 sk_?X_4$0)))) :named P31))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_4$0))
        (not (in$0 curr_3$0 sk_?X_4$0)))) :named P32))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0)) (not (in$0 a_1$0 sk_?X_4$0))
        (not (in$0 curr_3$0 sk_?X_4$0)))) :named P33))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_4$0)) (not (in$0 curr_3$0 sk_?X_4$0)))) :named P34))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_4$0)) (not (in$0 curr_3$0 sk_?X_4$0)))) :named P35))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_4$0)) (not (in$0 curr_3$0 sk_?X_4$0)))) :named P36))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_11$0)) (not (in$0 lst_1$0 sk_?X_11$0)))) :named P37))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_11$0))
        (not (in$0 lst_1$0 sk_?X_11$0)))) :named P38))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_11$0)) (not (in$0 lst_1$0 sk_?X_11$0)))) :named P39))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_11$0)) (not (in$0 lst_1$0 sk_?X_11$0)))) :named P40))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_11$0)) (not (in$0 lst_1$0 sk_?X_11$0)))) :named P41))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_11$0))
        (not (in$0 sk_l2_1$0 sk_?X_11$0)))) :named P42))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_11$0)) (not (in$0 sk_l2_1$0 sk_?X_11$0)))) :named P43))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_11$0)) (not (in$0 sk_l2_1$0 sk_?X_11$0)))) :named P44))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_11$0)) (not (in$0 sk_l2_1$0 sk_?X_11$0)))) :named P45))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_11$0)) (not (in$0 sk_l2_1$0 sk_?X_11$0)))) :named P46))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_11$0))
        (not (in$0 curr_3$0 sk_?X_11$0)))) :named P47))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0))
        (not (in$0 a_1$0 sk_?X_11$0)) (not (in$0 curr_3$0 sk_?X_11$0)))) :named P48))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_11$0)) (not (in$0 curr_3$0 sk_?X_11$0)))) :named P49))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_11$0)) (not (in$0 curr_3$0 sk_?X_11$0)))) :named P50))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_11$0)) (not (in$0 curr_3$0 sk_?X_11$0)))) :named P51))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_5$0)) (not (in$0 lst_1$0 sk_?X_5$0)))) :named P52))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_5$0))
        (not (in$0 lst_1$0 sk_?X_5$0)))) :named P53))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_5$0)) (not (in$0 lst_1$0 sk_?X_5$0)))) :named P54))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_5$0)) (not (in$0 lst_1$0 sk_?X_5$0)))) :named P55))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_5$0)) (not (in$0 lst_1$0 sk_?X_5$0)))) :named P56))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_5$0))
        (not (in$0 sk_l2_1$0 sk_?X_5$0)))) :named P57))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_5$0)) (not (in$0 sk_l2_1$0 sk_?X_5$0)))) :named P58))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_5$0)) (not (in$0 sk_l2_1$0 sk_?X_5$0)))) :named P59))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_5$0)) (not (in$0 sk_l2_1$0 sk_?X_5$0)))) :named P60))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_5$0)) (not (in$0 sk_l2_1$0 sk_?X_5$0)))) :named P61))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_5$0))
        (not (in$0 curr_3$0 sk_?X_5$0)))) :named P62))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0)) (not (in$0 a_1$0 sk_?X_5$0))
        (not (in$0 curr_3$0 sk_?X_5$0)))) :named P63))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_5$0)) (not (in$0 curr_3$0 sk_?X_5$0)))) :named P64))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_5$0)) (not (in$0 curr_3$0 sk_?X_5$0)))) :named P65))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_5$0)) (not (in$0 curr_3$0 sk_?X_5$0)))) :named P66))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 b$0 (ep$0 next$0 sk_?X_7$0 b$0) ?y)
            (not (Btwn$0 next$0 b$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P67))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 sk_?X_7$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P68))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_7$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P69))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a_1$0 (ep$0 next$0 sk_?X_7$0 a_1$0) ?y)
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P70))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_7$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P71))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_l1_1$0 (ep$0 next$0 sk_?X_7$0 sk_l1_1$0) ?y)
            (not (Btwn$0 next$0 sk_l1_1$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P72))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_l2_1$0 (ep$0 next$0 sk_?X_7$0 sk_l2_1$0) ?y)
            (not (Btwn$0 next$0 sk_l2_1$0 ?y ?y)) (not (in$0 ?y sk_?X_7$0)))) :named P73))

(assert (! (Btwn$0 next$0 b$0 (ep$0 next$0 sk_?X_7$0 b$0) (ep$0 next$0 sk_?X_7$0 b$0)) :named P74))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 sk_?X_7$0 lst_1$0)
  (ep$0 next$0 sk_?X_7$0 lst_1$0)) :named P75))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_7$0 curr_3$0)
  (ep$0 next$0 sk_?X_7$0 curr_3$0)) :named P76))

(assert (! (Btwn$0 next$0 a_1$0 (ep$0 next$0 sk_?X_7$0 a_1$0)
  (ep$0 next$0 sk_?X_7$0 a_1$0)) :named P77))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_7$0 prv_3$0)
  (ep$0 next$0 sk_?X_7$0 prv_3$0)) :named P78))

(assert (! (Btwn$0 next$0 sk_l1_1$0 (ep$0 next$0 sk_?X_7$0 sk_l1_1$0)
  (ep$0 next$0 sk_?X_7$0 sk_l1_1$0)) :named P79))

(assert (! (Btwn$0 next$0 sk_l2_1$0 (ep$0 next$0 sk_?X_7$0 sk_l2_1$0)
  (ep$0 next$0 sk_?X_7$0 sk_l2_1$0)) :named P80))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_9$0)) (not (in$0 lst_1$0 sk_?X_9$0)))) :named P81))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_9$0))
        (not (in$0 lst_1$0 sk_?X_9$0)))) :named P82))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_9$0)) (not (in$0 lst_1$0 sk_?X_9$0)))) :named P83))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_9$0)) (not (in$0 lst_1$0 sk_?X_9$0)))) :named P84))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_9$0)) (not (in$0 lst_1$0 sk_?X_9$0)))) :named P85))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_9$0))
        (not (in$0 sk_l2_1$0 sk_?X_9$0)))) :named P86))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_9$0)) (not (in$0 sk_l2_1$0 sk_?X_9$0)))) :named P87))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_9$0)) (not (in$0 sk_l2_1$0 sk_?X_9$0)))) :named P88))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_9$0)) (not (in$0 sk_l2_1$0 sk_?X_9$0)))) :named P89))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_9$0)) (not (in$0 sk_l2_1$0 sk_?X_9$0)))) :named P90))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_9$0))
        (not (in$0 curr_3$0 sk_?X_9$0)))) :named P91))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0)) (not (in$0 a_1$0 sk_?X_9$0))
        (not (in$0 curr_3$0 sk_?X_9$0)))) :named P92))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_9$0)) (not (in$0 curr_3$0 sk_?X_9$0)))) :named P93))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_9$0)) (not (in$0 curr_3$0 sk_?X_9$0)))) :named P94))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_9$0)) (not (in$0 curr_3$0 sk_?X_9$0)))) :named P95))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_10$0)) (not (in$0 lst_1$0 sk_?X_10$0)))) :named P96))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_10$0))
        (not (in$0 lst_1$0 sk_?X_10$0)))) :named P97))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_10$0)) (not (in$0 lst_1$0 sk_?X_10$0)))) :named P98))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_10$0)) (not (in$0 lst_1$0 sk_?X_10$0)))) :named P99))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_10$0)) (not (in$0 lst_1$0 sk_?X_10$0)))) :named P100))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_10$0))
        (not (in$0 sk_l2_1$0 sk_?X_10$0)))) :named P101))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_10$0)) (not (in$0 sk_l2_1$0 sk_?X_10$0)))) :named P102))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_10$0)) (not (in$0 sk_l2_1$0 sk_?X_10$0)))) :named P103))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_10$0)) (not (in$0 sk_l2_1$0 sk_?X_10$0)))) :named P104))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_10$0)) (not (in$0 sk_l2_1$0 sk_?X_10$0)))) :named P105))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_10$0))
        (not (in$0 curr_3$0 sk_?X_10$0)))) :named P106))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0))
        (not (in$0 a_1$0 sk_?X_10$0)) (not (in$0 curr_3$0 sk_?X_10$0)))) :named P107))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_10$0)) (not (in$0 curr_3$0 sk_?X_10$0)))) :named P108))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_10$0)) (not (in$0 curr_3$0 sk_?X_10$0)))) :named P109))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_10$0)) (not (in$0 curr_3$0 sk_?X_10$0)))) :named P110))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 lst_1$0) b$0) (not (= (read$0 next$0 b$0) lst_1$0))
        (not (in$0 b$0 sk_?X_8$0)) (not (in$0 lst_1$0 sk_?X_8$0)))) :named P111))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 lst_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) lst_1$0)) (not (in$0 a_1$0 sk_?X_8$0))
        (not (in$0 lst_1$0 sk_?X_8$0)))) :named P112))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 lst_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) lst_1$0))
        (not (in$0 prv_3$0 sk_?X_8$0)) (not (in$0 lst_1$0 sk_?X_8$0)))) :named P113))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 lst_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) lst_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_8$0)) (not (in$0 lst_1$0 sk_?X_8$0)))) :named P114))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 lst_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) lst_1$0))
        (not (in$0 curr_3$0 sk_?X_8$0)) (not (in$0 lst_1$0 sk_?X_8$0)))) :named P115))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) b$0)
        (not (= (read$0 next$0 b$0) sk_l2_1$0)) (not (in$0 b$0 sk_?X_8$0))
        (not (in$0 sk_l2_1$0 sk_?X_8$0)))) :named P116))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) sk_l2_1$0))
        (not (in$0 a_1$0 sk_?X_8$0)) (not (in$0 sk_l2_1$0 sk_?X_8$0)))) :named P117))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) sk_l2_1$0))
        (not (in$0 prv_3$0 sk_?X_8$0)) (not (in$0 sk_l2_1$0 sk_?X_8$0)))) :named P118))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_8$0)) (not (in$0 sk_l2_1$0 sk_?X_8$0)))) :named P119))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) sk_l2_1$0))
        (not (in$0 curr_3$0 sk_?X_8$0)) (not (in$0 sk_l2_1$0 sk_?X_8$0)))) :named P120))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_3$0) b$0)
        (not (= (read$0 next$0 b$0) curr_3$0)) (not (in$0 b$0 sk_?X_8$0))
        (not (in$0 curr_3$0 sk_?X_8$0)))) :named P121))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_3$0) a_1$0)
        (not (= (read$0 next$0 a_1$0) curr_3$0)) (not (in$0 a_1$0 sk_?X_8$0))
        (not (in$0 curr_3$0 sk_?X_8$0)))) :named P122))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_8$0)) (not (in$0 curr_3$0 sk_?X_8$0)))) :named P123))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_3$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_3$0))
        (not (in$0 sk_l1_1$0 sk_?X_8$0)) (not (in$0 curr_3$0 sk_?X_8$0)))) :named P124))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_8$0)) (not (in$0 curr_3$0 sk_?X_8$0)))) :named P125))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P126))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P127))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_6$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_6$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0)))))) :named P128))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_10$0 FP_Caller$0))
                 (or (in$0 x sk_?X_10$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_10$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_10$0 FP_Caller$0)))))) :named P129))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))) :named P130))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_4$0 sk_?X_5$0))
                 (or (in$0 x sk_?X_4$0) (in$0 x sk_?X_5$0)))
            (and (not (in$0 x sk_?X_4$0)) (not (in$0 x sk_?X_5$0))
                 (not (in$0 x (union$0 sk_?X_4$0 sk_?X_5$0)))))) :named P131))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P132))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_9$0 sk_?X_10$0))
                 (or (in$0 x sk_?X_9$0) (in$0 x sk_?X_10$0)))
            (and (not (in$0 x sk_?X_9$0)) (not (in$0 x sk_?X_10$0))
                 (not (in$0 x (union$0 sk_?X_9$0 sk_?X_10$0)))))) :named P133))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_7$0 sk_?X_10$0))
                 (or (in$0 x sk_?X_7$0) (in$0 x sk_?X_10$0)))
            (and (not (in$0 x sk_?X_7$0)) (not (in$0 x sk_?X_10$0))
                 (not (in$0 x (union$0 sk_?X_7$0 sk_?X_10$0)))))) :named P134))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P135))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_9$0) (in$0 x sk_?X_10$0)
                 (in$0 x (intersection$0 sk_?X_9$0 sk_?X_10$0)))
            (and (or (not (in$0 x sk_?X_9$0)) (not (in$0 x sk_?X_10$0)))
                 (not (in$0 x (intersection$0 sk_?X_9$0 sk_?X_10$0)))))) :named P136))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_4$0) (in$0 x sk_?X_5$0)
                 (in$0 x (intersection$0 sk_?X_4$0 sk_?X_5$0)))
            (and (or (not (in$0 x sk_?X_4$0)) (not (in$0 x sk_?X_5$0)))
                 (not (in$0 x (intersection$0 sk_?X_4$0 sk_?X_5$0)))))) :named P137))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_10$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_10$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_10$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_10$0)))))) :named P138))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_7$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_7$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_7$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_7$0)))))) :named P139))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P140))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_10$0)
                 (in$0 x (setminus$0 sk_?X_10$0 sk_?X_7$0))
                 (not (in$0 x sk_?X_7$0)))
            (and (or (in$0 x sk_?X_7$0) (not (in$0 x sk_?X_10$0)))
                 (not (in$0 x (setminus$0 sk_?X_10$0 sk_?X_7$0)))))) :named P141))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_10$0))
                 (not (in$0 x sk_?X_10$0)))
            (and (or (in$0 x sk_?X_10$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_10$0)))))) :named P142))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P143))

(assert (! (= (read$0 next$0 null$0) null$0) :named P144))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P145))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P146))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_1$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 b_1$0 sk_?X_5$0))
             (and (= curr_3$0 null$0) (= prv_3$0 b_1$0)))
         Axiom_4$0)
    (not
         (dlseg_struct$0 sk_?X_5$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           b_1$0))) :named P147))

(assert (! (or
    (and (Btwn$0 next$0 lst$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 lst$0) a$0) (in$0 b$0 sk_?X_11$0))
             (and (= a$0 b$0) (= lst$0 null$0)))
         Axiom_6$0)
    (not (dlseg_struct$0 sk_?X_11$0 next$0 prev$0 lst$0 a$0 null$0 b$0))) :named P148))

(assert (! (or
    (and (Btwn$0 next$0 lst_1$0 curr_3$0 curr_3$0)
         (or
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 lst_1$0) a_1$0) (in$0 prv_3$0 sk_?X_4$0))
             (and (= a_1$0 prv_3$0) (= lst_1$0 curr_3$0)))
         Axiom_8$0)
    (not
         (dlseg_struct$0 sk_?X_4$0 next$0 prev$0 lst_1$0 a_1$0 curr_3$0
           prv_3$0))) :named P149))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P150))

(assert (! (= a_1$0 a$0) :named P151))

(assert (! (= curr_2$0 lst$0) :named P152))

(assert (! (= lst_1$0 lst$0) :named P153))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P154))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P155))

(assert (! (= emptyset$0 (intersection$0 sk_?X_4$0 sk_?X_5$0)) :named P156))

(assert (! (= sk_?X_5$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 b_1$0)) :named P157))

(assert (! (= sk_?X_6$0 (union$0 sk_?X_4$0 sk_?X_5$0)) :named P158))

(assert (! (dlseg_struct$0 sk_?X_5$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 b_1$0) :named P159))

(assert (! (= sk_?X_7$0 (union$0 sk_?X_9$0 sk_?X_8$0)) :named P160))

(assert (! (= sk_?X_8$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0)) :named P161))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P162))

(assert (! (dlseg_struct$0 sk_?X_9$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0) :named P163))

(assert (! (= sk_?X_10$0 (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0)) :named P164))

(assert (! (dlseg_struct$0 sk_?X_10$0 next$0 prev$0 lst$0 a$0 null$0 b$0) :named P165))

(assert (! (or
    (and (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0) (in$0 sk_l1_1$0 sk_?X_11$0)
         (in$0 sk_l2_1$0 sk_?X_11$0)
         (not (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)))
    (and (in$0 sk_l2_1$0 (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0))
         (not (in$0 sk_l2_1$0 sk_?X_11$0)))
    (and (in$0 sk_l2_1$0 sk_?X_11$0)
         (not
              (in$0 sk_l2_1$0
                (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0))))
    (and
         (or (not (= (read$0 next$0 b$0) null$0))
             (not (= (read$0 prev$0 lst$0) a$0)) (not (in$0 b$0 sk_?X_11$0)))
         (or (not (= a$0 b$0)) (not (= lst$0 null$0))))
    (not (Btwn$0 next$0 lst$0 null$0 null$0))) :named P166))

(assert (! (not (in$0 null$0 Alloc$0)) :named P167))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                     b_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                          b_1$0)))))) :named P168))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0
                          prv_2$0)))))) :named P169))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0) (in$0 b$0 sk_?X_8$0))
             (and (= curr_2$0 null$0) (= prv_2$0 b$0)))
         Axiom_3$0)
    (not
         (dlseg_struct$0 sk_?X_8$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0))) :named P170))

(assert (! (or
    (and (Btwn$0 next$0 lst$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 lst$0) a$0) (in$0 b$0 sk_?X_10$0))
             (and (= a$0 b$0) (= lst$0 null$0)))
         Axiom_5$0)
    (not (dlseg_struct$0 sk_?X_10$0 next$0 prev$0 lst$0 a$0 null$0 b$0))) :named P171))

(assert (! (or
    (and (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
         (or
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 lst$0) a$0) (in$0 prv_2$0 sk_?X_9$0))
             (and (= a$0 prv_2$0) (= lst$0 curr_2$0)))
         Axiom_7$0)
    (not (dlseg_struct$0 sk_?X_9$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0))) :named P172))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P173))

(assert (! (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)) :named P174))

(assert (! (= b_1$0 b$0) :named P175))

(assert (! (= curr_3$0 null$0) :named P176))

(assert (! (= prv_2$0 a$0) :named P177))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P178))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P179))

(assert (! (= sk_?X_4$0 (dlseg_domain$0 next$0 prev$0 lst_1$0 a_1$0 curr_3$0 prv_3$0)) :named P180))

(assert (! (= sk_?X_6$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P181))

(assert (! (dlseg_struct$0 sk_?X_4$0 next$0 prev$0 lst_1$0 a_1$0 curr_3$0 prv_3$0) :named P182))

(assert (! (= emptyset$0 (intersection$0 sk_?X_9$0 sk_?X_8$0)) :named P183))

(assert (! (= sk_?X_7$0 FP_1$0) :named P184))

(assert (! (= sk_?X_9$0 (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0)) :named P185))

(assert (! (dlseg_struct$0 sk_?X_8$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0) :named P186))

(assert (! (= sk_?X_10$0 FP$0) :named P187))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P188))

(assert (! (= sk_?X_11$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))) :named P189))

(assert (! (not (in$0 null$0 Alloc$0)) :named P190))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          b$0)))))) :named P191))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0)))))) :named P192))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 curr_3$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 lst_1$0 a_1$0 curr_3$0
                     prv_3$0))
                 (not (= l1 curr_3$0)))
            (and
                 (or (= l1 curr_3$0)
                     (not (Btwn$0 next$0 lst_1$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 lst_1$0 a_1$0 curr_3$0
                          prv_3$0)))))) :named P193))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P194))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P195))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P196))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P197))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P198))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P199))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P200))

(check-sat)

(get-interpolants (and P86 P37 P148 P140 P58 P151 P43 P50 P35 P100 P20 P56 P87 P110 P107 P19 P131 P108 P145 P90 P25 P109 P178 P59 P186 P200 P95 P119 P155 P144 P48 P75 P88 P29 P4 P28 P146 P54 P31 P80 P85 P96 P3 P7 P184 P130 P12 P106 P102 P114 P182 P76 P13 P39 P1 P170 P42 P141 P65 P53 P32 P124 P172 P136 P30 P123 P149 P189 P117 P116 P120 P36 P127 P158 P156 P138 P161 P137 P17 P111 P89 P105 P38 P195 P113 P168 P132 P104 P163 P188 P125 P24 P66 P177 P193 P157 P101 P47 P69 P51 P92) (and P70 P40 P15 P197 P135 P180 P68 P62 P14 P129 P5 P21 P191 P18 P134 P11 P6 P73 P52 P27 P33 P63 P94 P198 P126 P81 P112 P93 P121 P175 P16 P103 P159 P83 P128 P166 P49 P187 P171 P122 P199 P181 P22 P133 P44 P165 P61 P142 P91 P153 P9 P46 P196 P167 P8 P84 P176 P82 P26 P118 P194 P160 P183 P78 P64 P154 P97 P10 P23 P74 P139 P72 P143 P71 P0 P98 P79 P150 P45 P2 P115 P67 P147 P179 P192 P41 P185 P55 P164 P60 P173 P162 P99 P190 P174 P152 P34 P57 P169 P77))

(exit)