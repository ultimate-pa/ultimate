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
  tests/spl/sl/rec_copy.spl:38:4-27:A postcondition of procedure rec_copy_loop might not hold at this return point
  tests/spl/sl/rec_copy.spl:35:10-46:Related location: This is the postcondition that might not hold
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
(declare-fun FP$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_7$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun FP_Caller_final_4$0 () SetLoc)
(declare-fun cp$0 () Loc)
(declare-fun curr$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_4$0 () FldLoc)
(declare-fun res_8$0 () Loc)
(declare-fun res_9$0 () Loc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun sk_?X_34$0 () SetLoc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr$0 ?y ?y)) (= curr$0 ?y)
            (Btwn$0 next$0 curr$0 (read$0 next$0 curr$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 curr$0 ?y ?y)) (= curr$0 ?y)
            (Btwn$0 next_4$0 curr$0 (read$0 next_4$0 curr$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr$0) curr$0))
            (not (Btwn$0 next$0 curr$0 ?y ?y)) (= curr$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 curr$0) curr$0))
            (not (Btwn$0 next_4$0 curr$0 ?y ?y)) (= curr$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 curr$0 (read$0 next$0 curr$0) (read$0 next$0 curr$0)) :named P4))

(assert (! (Btwn$0 next_4$0 curr$0 (read$0 next_4$0 curr$0) (read$0 next_4$0 curr$0)) :named P5))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 next$0 curr$0) (read$0 next_4$0 curr$0))
        (not (in$0 curr$0 (setminus$0 Alloc$0 FP_6$0))))) :named P6))

(assert (! (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 cp$0 ?z ?y) (Btwn$0 next_4$0 cp$0 ?z ?y))
                (and (not (Btwn$0 next$0 cp$0 ?z ?y))
                     (not (Btwn$0 next_4$0 cp$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 cp$0 ?y (ep$0 next$0 FP_6$0 cp$0))
                         (and (Btwn$0 next$0 cp$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 cp$0
                                     (ep$0 next$0 FP_6$0 cp$0)
                                     (ep$0 next$0 FP_6$0 cp$0))))))))) :named P7))

(assert (! (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 curr$0 ?z ?y)
                     (Btwn$0 next_4$0 curr$0 ?z ?y))
                (and (not (Btwn$0 next$0 curr$0 ?z ?y))
                     (not (Btwn$0 next_4$0 curr$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 curr$0 ?y
                           (ep$0 next$0 FP_6$0 curr$0))
                         (and (Btwn$0 next$0 curr$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 curr$0
                                     (ep$0 next$0 FP_6$0 curr$0)
                                     (ep$0 next$0 FP_6$0 curr$0))))))))) :named P8))

(assert (! (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 res_8$0 ?z ?y)
                     (Btwn$0 next_4$0 res_8$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_8$0 ?z ?y))
                     (not (Btwn$0 next_4$0 res_8$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 res_8$0 ?y
                           (ep$0 next$0 FP_6$0 res_8$0))
                         (and (Btwn$0 next$0 res_8$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 res_8$0
                                     (ep$0 next$0 FP_6$0 res_8$0)
                                     (ep$0 next$0 FP_6$0 res_8$0))))))))) :named P9))

(assert (! (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_3$0 ?z ?y)
                     (Btwn$0 next_4$0 sk_?e_3$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_3$0 ?z ?y))
                     (not (Btwn$0 next_4$0 sk_?e_3$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_3$0 ?y
                           (ep$0 next$0 FP_6$0 sk_?e_3$0))
                         (and (Btwn$0 next$0 sk_?e_3$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_3$0
                                     (ep$0 next$0 FP_6$0 sk_?e_3$0)
                                     (ep$0 next$0 FP_6$0 sk_?e_3$0))))))))) :named P10))

(assert (! (or (not Axiom_3$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 cp$0 FP_6$0)
                (and (Btwn$0 next$0 cp$0 ?z ?y) (Btwn$0 next_4$0 cp$0 ?z ?y))
                (and (not (Btwn$0 next$0 cp$0 ?z ?y))
                     (not (Btwn$0 next_4$0 cp$0 ?z ?y)))
                (not (= cp$0 (ep$0 next$0 FP_6$0 cp$0)))))) :named P11))

(assert (! (or (not Axiom_3$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 curr$0 FP_6$0)
                (and (Btwn$0 next$0 curr$0 ?z ?y)
                     (Btwn$0 next_4$0 curr$0 ?z ?y))
                (and (not (Btwn$0 next$0 curr$0 ?z ?y))
                     (not (Btwn$0 next_4$0 curr$0 ?z ?y)))
                (not (= curr$0 (ep$0 next$0 FP_6$0 curr$0)))))) :named P12))

(assert (! (or (not Axiom_3$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 res_8$0 FP_6$0)
                (and (Btwn$0 next$0 res_8$0 ?z ?y)
                     (Btwn$0 next_4$0 res_8$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_8$0 ?z ?y))
                     (not (Btwn$0 next_4$0 res_8$0 ?z ?y)))
                (not (= res_8$0 (ep$0 next$0 FP_6$0 res_8$0)))))) :named P13))

(assert (! (or (not Axiom_3$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_3$0 FP_6$0)
                (and (Btwn$0 next$0 sk_?e_3$0 ?z ?y)
                     (Btwn$0 next_4$0 sk_?e_3$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_3$0 ?z ?y))
                     (not (Btwn$0 next_4$0 sk_?e_3$0 ?z ?y)))
                (not (= sk_?e_3$0 (ep$0 next$0 FP_6$0 sk_?e_3$0)))))) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 cp$0 (ep$0 next$0 sk_?X_29$0 cp$0) ?y)
            (not (Btwn$0 next$0 cp$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr$0 (ep$0 next$0 sk_?X_29$0 curr$0) ?y)
            (not (Btwn$0 next$0 curr$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 res_8$0 (ep$0 next$0 sk_?X_29$0 res_8$0) ?y)
            (not (Btwn$0 next$0 res_8$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_3$0 (ep$0 next$0 sk_?X_29$0 sk_?e_3$0) ?y)
            (not (Btwn$0 next$0 sk_?e_3$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 cp$0) sk_?X_29$0)
    (= cp$0 (ep$0 next$0 sk_?X_29$0 cp$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 curr$0) sk_?X_29$0)
    (= curr$0 (ep$0 next$0 sk_?X_29$0 curr$0))) :named P20))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 res_8$0) sk_?X_29$0)
    (= res_8$0 (ep$0 next$0 sk_?X_29$0 res_8$0))) :named P21))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 sk_?e_3$0) sk_?X_29$0)
    (= sk_?e_3$0 (ep$0 next$0 sk_?X_29$0 sk_?e_3$0))) :named P22))

(assert (! (Btwn$0 next$0 cp$0 (ep$0 next$0 sk_?X_29$0 cp$0)
  (ep$0 next$0 sk_?X_29$0 cp$0)) :named P23))

(assert (! (Btwn$0 next$0 curr$0 (ep$0 next$0 sk_?X_29$0 curr$0)
  (ep$0 next$0 sk_?X_29$0 curr$0)) :named P24))

(assert (! (Btwn$0 next$0 res_8$0 (ep$0 next$0 sk_?X_29$0 res_8$0)
  (ep$0 next$0 sk_?X_29$0 res_8$0)) :named P25))

(assert (! (Btwn$0 next$0 sk_?e_3$0 (ep$0 next$0 sk_?X_29$0 sk_?e_3$0)
  (ep$0 next$0 sk_?X_29$0 sk_?e_3$0)) :named P26))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_7$0 Alloc$0))
                 (or (in$0 x FP_7$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_7$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_7$0 Alloc$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 sk_?X_31$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x sk_?X_31$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_31$0))
                 (not (in$0 x (union$0 sk_?X_29$0 sk_?X_31$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 FP$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_29$0 FP$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_6$0) sk_?X_33$0))
                 (or (in$0 x (setminus$0 FP$0 FP_6$0)) (in$0 x sk_?X_33$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_6$0)))
                 (not (in$0 x sk_?X_33$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_6$0) sk_?X_33$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_2$0 FP_7$0))
                 (or (in$0 x FP_Caller_2$0) (in$0 x FP_7$0)))
            (and (not (in$0 x FP_Caller_2$0)) (not (in$0 x FP_7$0))
                 (not (in$0 x (union$0 FP_Caller_2$0 FP_7$0)))))) :named P34))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_6$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_6$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_6$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_6$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_33$0 sk_?X_34$0))
                 (or (in$0 x sk_?X_33$0) (in$0 x sk_?X_34$0)))
            (and (not (in$0 x sk_?X_33$0)) (not (in$0 x sk_?X_34$0))
                 (not (in$0 x (union$0 sk_?X_33$0 sk_?X_34$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_29$0) (in$0 x sk_?X_31$0)
                 (in$0 x (intersection$0 sk_?X_29$0 sk_?X_31$0)))
            (and (or (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_31$0)))
                 (not (in$0 x (intersection$0 sk_?X_29$0 sk_?X_31$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_29$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_29$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_33$0) (in$0 x sk_?X_34$0)
                 (in$0 x (intersection$0 sk_?X_33$0 sk_?X_34$0)))
            (and (or (not (in$0 x sk_?X_33$0)) (not (in$0 x sk_?X_34$0)))
                 (not (in$0 x (intersection$0 sk_?X_33$0 sk_?X_34$0)))))) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P41))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_29$0))
                 (not (in$0 x sk_?X_29$0)))
            (and (or (in$0 x sk_?X_29$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_29$0)))))) :named P42))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_29$0))
                 (not (in$0 x sk_?X_29$0)))
            (and (or (in$0 x sk_?X_29$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_29$0)))))) :named P43))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P44))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P45))

(assert (! (= (read$0 next$0 null$0) null$0) :named P46))

(assert (! (= (read$0 next_4$0 null$0) null$0) :named P47))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P48))

(assert (! (or (Btwn$0 next$0 cp$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_29$0 next$0 cp$0 null$0))) :named P49))

(assert (! (or (Btwn$0 next$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_31$0 next$0 curr$0 null$0))) :named P50))

(assert (! (or (Btwn$0 next_4$0 res_8$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_28$0 next_4$0 res_8$0 null$0))) :named P51))

(assert (! (= FP_7$0
  (union$0 (setminus$0 FP$0 FP_6$0)
    (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0)))) :named P52))

(assert (! (= FP_Caller_final_4$0 (union$0 FP_Caller_2$0 FP_7$0)) :named P53))

(assert (! (= res_9$0 res_8$0) :named P54))

(assert (! (= Alloc$0 (union$0 FP_7$0 Alloc$0)) :named P55))

(assert (! (= emptyset$0 (intersection$0 sk_?X_32$0 sk_?X_31$0)) :named P56))

(assert (! (= sk_?X_30$0 FP$0) :named P57))

(assert (! (= sk_?X_32$0 (lseg_domain$0 next$0 cp$0 null$0)) :named P58))

(assert (! (lseg_struct$0 sk_?X_31$0 next$0 curr$0 null$0) :named P59))

(assert (! (= sk_?X_28$0
  (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0))) :named P60))

(assert (! (lseg_struct$0 sk_?X_28$0 next_4$0 res_8$0 null$0) :named P61))

(assert (! (= sk_?X_29$0 (lseg_domain$0 next$0 cp$0 null$0)) :named P62))

(assert (! (lseg_struct$0 sk_?X_29$0 next$0 cp$0 null$0) :named P63))

(assert (! (= sk_?X_34$0 (lseg_domain$0 next_4$0 curr$0 null$0)) :named P64))

(assert (! (or (in$0 sk_?e_3$0 (intersection$0 sk_?X_33$0 sk_?X_34$0))
    (and
         (in$0 sk_?e_3$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_3$0 sk_?X_35$0)))
    (and (in$0 sk_?e_3$0 sk_?X_35$0)
         (not
              (in$0 sk_?e_3$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (not (Btwn$0 next_4$0 curr$0 null$0 null$0))
    (not (Btwn$0 next_4$0 res_9$0 null$0 null$0))) :named P65))

(assert (! (not (in$0 null$0 Alloc$0)) :named P66))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0)))))) :named P67))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 res_8$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_4$0 res_8$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_4$0 res_8$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_4$0 res_8$0 null$0)))))) :named P68))

(assert (! (or (and Axiom_5$0 Axiom_4$0 Axiom_3$0)
    (not (Frame$0 FP_6$0 Alloc$0 next$0 next_4$0))) :named P69))

(assert (! (or (Btwn$0 next$0 cp$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_32$0 next$0 cp$0 null$0))) :named P70))

(assert (! (or (Btwn$0 next_4$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_34$0 next_4$0 curr$0 null$0))) :named P71))

(assert (! (or (Btwn$0 next_4$0 res_9$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_33$0 next_4$0 res_9$0 null$0))) :named P72))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P73))

(assert (! (= curr$0 null$0) :named P74))

(assert (! (Frame$0 FP_6$0 Alloc$0 next$0 next_4$0) :named P75))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P76))

(assert (! (= sk_?X_30$0 (union$0 sk_?X_32$0 sk_?X_31$0)) :named P77))

(assert (! (= sk_?X_31$0 (lseg_domain$0 next$0 curr$0 null$0)) :named P78))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P79))

(assert (! (lseg_struct$0 sk_?X_32$0 next$0 cp$0 null$0) :named P80))

(assert (! (= sk_?X_28$0 (lseg_domain$0 next_4$0 res_8$0 null$0)) :named P81))

(assert (! (= sk_?X_29$0 FP_6$0) :named P82))

(assert (! (= FP$0 (union$0 FP_6$0 FP$0)) :named P83))

(assert (! (= sk_?X_33$0 (lseg_domain$0 next_4$0 res_9$0 null$0)) :named P84))

(assert (! (= sk_?X_35$0 (union$0 sk_?X_33$0 sk_?X_34$0)) :named P85))

(assert (! (not (in$0 null$0 Alloc$0)) :named P86))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 cp$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 cp$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0)))))) :named P87))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_4$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_4$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_4$0 curr$0 null$0)))))) :named P88))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 res_9$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_4$0 res_9$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_4$0 res_9$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_4$0 res_9$0 null$0)))))) :named P89))

(assert (! (forall ((?x Loc)) (Btwn$0 next_4$0 ?x ?x ?x)) :named P90))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P91))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_4$0 ?x ?y ?x)) (= ?x ?y))) :named P92))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P93))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?x ?z ?z))
            (Btwn$0 next_4$0 ?x ?y ?z) (Btwn$0 next_4$0 ?x ?z ?y))) :named P94))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P95))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?y) (Btwn$0 next_4$0 ?y ?z ?z)))) :named P96))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P97))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?y ?z ?z))
            (Btwn$0 next_4$0 ?x ?z ?z))) :named P98))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P99))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?y ?u ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?u) (Btwn$0 next_4$0 ?x ?u ?z)))) :named P100))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P101))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?x ?u ?y))
            (and (Btwn$0 next_4$0 ?x ?u ?z) (Btwn$0 next_4$0 ?u ?y ?z)))) :named P102))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P103))

(check-sat)

(get-interpolants (and P71 P100 P80 P7 P83 P4 P8 P60 P62 P12 P63 P49 P36 P39 P29 P81 P26 P22 P48 P5 P90 P52 P84 P34 P79 P70 P43 P19 P16 P15 P99 P61 P87 P30 P57 P86 P68 P69 P10 P21 P37 P102 P89 P95 P65 P94 P103 P41 P38 P17 P92 P25) (and P56 P55 P24 P58 P35 P33 P54 P98 P78 P88 P93 P82 P40 P53 P72 P11 P96 P18 P13 P23 P44 P97 P45 P0 P85 P6 P77 P3 P59 P47 P42 P14 P1 P73 P9 P31 P27 P46 P101 P67 P76 P66 P28 P50 P91 P2 P32 P74 P75 P51 P64 P20))

(exit)