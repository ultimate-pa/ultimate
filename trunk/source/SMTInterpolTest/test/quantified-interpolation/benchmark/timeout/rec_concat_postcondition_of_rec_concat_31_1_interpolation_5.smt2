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
  tests/spl/sl/rec_concat.spl:31:1-2:A postcondition of procedure rec_concat might not hold at this return point
  tests/spl/sl/rec_concat.spl:26:10-23:Related location: This is the postcondition that might not hold
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
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun FP_Caller_final_4$0 () SetLoc)
(declare-fun a_1$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun l_5$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun sk_?X_52$0 () SetLoc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun sk_?X_55$0 () SetLoc)
(declare-fun sk_?X_56$0 () SetLoc)
(declare-fun sk_?X_57$0 () SetLoc)
(declare-fun sk_?X_58$0 () SetLoc)
(declare-fun sk_?X_59$0 () SetLoc)
(declare-fun sk_?X_60$0 () SetLoc)
(declare-fun sk_?X_61$0 () SetLoc)
(declare-fun sk_?X_62$0 () SetLoc)
(declare-fun sk_?e_4$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 l_5$0 ?y ?y)) (= l_5$0 ?y)
            (Btwn$0 next$0 l_5$0 (read$0 next$0 l_5$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 l_5$0) l_5$0))
            (not (Btwn$0 next$0 l_5$0 ?y ?y)) (= l_5$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 l_5$0 (read$0 next$0 l_5$0) (read$0 next$0 l_5$0)) :named P4))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P5))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_3$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P6))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP_3$0 a_1$0) ?y)
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P7))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 b$0 (ep$0 next$0 FP_3$0 b$0) ?y)
            (not (Btwn$0 next$0 b$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P8))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_3$0 sk_?e_4$0) ?y)
            (not (Btwn$0 next$0 sk_?e_4$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P9))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 null$0) FP_3$0)
    (= null$0 (ep$0 next$0 FP_3$0 null$0))) :named P10))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 a_1$0) FP_3$0)
    (= a_1$0 (ep$0 next$0 FP_3$0 a_1$0))) :named P11))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 b$0) FP_3$0) (= b$0 (ep$0 next$0 FP_3$0 b$0))) :named P12))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 sk_?e_4$0) FP_3$0)
    (= sk_?e_4$0 (ep$0 next$0 FP_3$0 sk_?e_4$0))) :named P13))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_3$0 null$0)
  (ep$0 next$0 FP_3$0 null$0)) :named P14))

(assert (! (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP_3$0 a_1$0) (ep$0 next$0 FP_3$0 a_1$0)) :named P15))

(assert (! (Btwn$0 next$0 b$0 (ep$0 next$0 FP_3$0 b$0) (ep$0 next$0 FP_3$0 b$0)) :named P16))

(assert (! (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_3$0 sk_?e_4$0)
  (ep$0 next$0 FP_3$0 sk_?e_4$0)) :named P17))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P18))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_4$0 Alloc$0))
                 (or (in$0 x FP_4$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_4$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_4$0 Alloc$0)))))) :named P19))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 sk_?X_53$0))
                 (or (in$0 x FP_3$0) (in$0 x sk_?X_53$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x sk_?X_53$0))
                 (not (in$0 x (union$0 FP_3$0 sk_?X_53$0)))))) :named P20))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 FP$0))
                 (or (in$0 x FP_3$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_3$0 FP$0)))))) :named P21))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_3$0) sk_?X_59$0))
                 (or (in$0 x (setminus$0 FP$0 FP_3$0)) (in$0 x sk_?X_59$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_3$0)))
                 (not (in$0 x sk_?X_59$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_3$0) sk_?X_59$0)))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_2$0 FP_4$0))
                 (or (in$0 x FP_Caller_2$0) (in$0 x FP_4$0)))
            (and (not (in$0 x FP_Caller_2$0)) (not (in$0 x FP_4$0))
                 (not (in$0 x (union$0 FP_Caller_2$0 FP_4$0)))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_56$0 sk_?X_57$0))
                 (or (in$0 x sk_?X_56$0) (in$0 x sk_?X_57$0)))
            (and (not (in$0 x sk_?X_56$0)) (not (in$0 x sk_?X_57$0))
                 (not (in$0 x (union$0 sk_?X_56$0 sk_?X_57$0)))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_3$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_3$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_3$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_3$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P26))

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
            (and (in$0 x sk_?X_56$0) (in$0 x sk_?X_57$0)
                 (in$0 x (intersection$0 sk_?X_56$0 sk_?X_57$0)))
            (and (or (not (in$0 x sk_?X_56$0)) (not (in$0 x sk_?X_57$0)))
                 (not (in$0 x (intersection$0 sk_?X_56$0 sk_?X_57$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_3$0) (in$0 x sk_?X_53$0)
                 (in$0 x (intersection$0 FP_3$0 sk_?X_53$0)))
            (and (or (not (in$0 x FP_3$0)) (not (in$0 x sk_?X_53$0)))
                 (not (in$0 x (intersection$0 FP_3$0 sk_?X_53$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_3$0)
                 (in$0 x (intersection$0 Alloc$0 FP_3$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_3$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_3$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_3$0))
                 (not (in$0 x FP_3$0)))
            (and (or (in$0 x FP_3$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_3$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P34))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P35))

(assert (! (= (read$0 (write$0 next$0 l_5$0 b$0) l_5$0) b$0) :named P36))

(assert (! (or (= l_5$0 l_5$0)
    (= (read$0 next$0 l_5$0) (read$0 (write$0 next$0 l_5$0 b$0) l_5$0))) :named P37))

(assert (! (or (= null$0 l_5$0)
    (= (read$0 next$0 null$0) (read$0 (write$0 next$0 l_5$0 b$0) null$0))) :named P38))

(assert (! (= (read$0 next$0 null$0) null$0) :named P39))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P40))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P41))

(assert (! (or (Btwn$0 next$0 a_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_55$0 next$0 a_1$0 null$0))) :named P42))

(assert (! (or (Btwn$0 next$0 a_1$0 l_5$0 l_5$0)
    (not (lseg_struct$0 sk_?X_56$0 next$0 a_1$0 l_5$0))) :named P43))

(assert (! (or (Btwn$0 next_1$0 a_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_62$0 next_1$0 a_1$0 null$0))) :named P44))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P45))

(assert (! (= next_1$0 (write$0 next$0 l_5$0 b$0)) :named P46))

(assert (! (= Alloc$0 (union$0 FP_4$0 Alloc$0)) :named P47))

(assert (! (= (read$0 next$0 l_5$0) null$0) :named P48))

(assert (! (= emptyset$0 (intersection$0 sk_?X_56$0 sk_?X_58$0)) :named P49))

(assert (! (= sk_?X_57$0 (setenum$0 l_5$0)) :named P50))

(assert (! (= sk_?X_59$0
  (union$0 (intersection$0 Alloc$0 FP_3$0) (setminus$0 Alloc$0 Alloc$0))) :named P51))

(assert (! (lseg_struct$0 sk_?X_56$0 next$0 a_1$0 l_5$0) :named P52))

(assert (! (= emptyset$0 (intersection$0 sk_?X_54$0 sk_?X_53$0)) :named P53))

(assert (! (= sk_?X_52$0 FP$0) :named P54))

(assert (! (= sk_?X_54$0 sk_?X_55$0) :named P55))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P56))

(assert (! (lseg_struct$0 sk_?X_55$0 next$0 a_1$0 null$0) :named P57))

(assert (! (= emptyset$0 emptyset$0) :named P58))

(assert (! (= sk_?X_60$0 FP_3$0) :named P59))

(assert (! (= FP$0 (union$0 FP_3$0 FP$0)) :named P60))

(assert (! (not (= a_1$0 null$0)) :named P61))

(assert (! (or
    (and (in$0 sk_?e_4$0 (lseg_domain$0 next_1$0 a_1$0 null$0))
         (not (in$0 sk_?e_4$0 sk_?X_62$0)))
    (and (in$0 sk_?e_4$0 sk_?X_62$0)
         (not (in$0 sk_?e_4$0 (lseg_domain$0 next_1$0 a_1$0 null$0))))
    (not (Btwn$0 next_1$0 a_1$0 null$0 null$0))) :named P62))

(assert (! (not (in$0 null$0 Alloc$0)) :named P63))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 l_5$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_1$0 l_5$0))
                 (not (= l1 l_5$0)))
            (and (or (= l1 l_5$0) (not (Btwn$0 next$0 a_1$0 l1 l_5$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_1$0 l_5$0)))))) :named P64))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 a_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 a_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 a_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 a_1$0 null$0)))))) :named P65))

(assert (! (or (Btwn$0 next$0 a_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_61$0 next$0 a_1$0 null$0))) :named P66))

(assert (! (or (Btwn$0 next$0 b$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_53$0 next$0 b$0 null$0))) :named P67))

(assert (! (= FP_4$0
  (union$0 (setminus$0 FP$0 FP_3$0)
    (union$0 (intersection$0 Alloc$0 FP_3$0) (setminus$0 Alloc$0 Alloc$0)))) :named P68))

(assert (! (= FP_Caller_final_4$0 (union$0 FP_Caller_2$0 FP_4$0)) :named P69))

(assert (! (Frame$0 FP_3$0 Alloc$0 next$0 next$0) :named P70))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P71))

(assert (! (= emptyset$0 emptyset$0) :named P72))

(assert (! (= sk_?X_56$0 (lseg_domain$0 next$0 a_1$0 l_5$0)) :named P73))

(assert (! (= sk_?X_58$0 sk_?X_57$0) :named P74))

(assert (! (= sk_?X_59$0 (union$0 sk_?X_56$0 sk_?X_58$0)) :named P75))

(assert (! (= emptyset$0 emptyset$0) :named P76))

(assert (! (= sk_?X_52$0 (union$0 sk_?X_54$0 sk_?X_53$0)) :named P77))

(assert (! (= sk_?X_53$0 (lseg_domain$0 next$0 b$0 null$0)) :named P78))

(assert (! (= sk_?X_55$0 (lseg_domain$0 next$0 a_1$0 null$0)) :named P79))

(assert (! (lseg_struct$0 sk_?X_53$0 next$0 b$0 null$0) :named P80))

(assert (! (not (= a_1$0 null$0)) :named P81))

(assert (! (= sk_?X_60$0 sk_?X_61$0) :named P82))

(assert (! (= sk_?X_61$0 (lseg_domain$0 next$0 a_1$0 null$0)) :named P83))

(assert (! (lseg_struct$0 sk_?X_61$0 next$0 a_1$0 null$0) :named P84))

(assert (! (= sk_?X_62$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))) :named P85))

(assert (! (not (in$0 null$0 Alloc$0)) :named P86))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_1$0 null$0)))))) :named P87))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 b$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 b$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 b$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 b$0 null$0)))))) :named P88))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 l_5$0 b$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v l_5$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z l_5$0 l_5$0)))))
                          (and (not (= l_5$0 ?v))
                               (or (Btwn$0 next$0 ?z l_5$0 ?v)
                                   (and (Btwn$0 next$0 ?z l_5$0 l_5$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u l_5$0)
                               (or (Btwn$0 next$0 b$0 ?v l_5$0)
                                   (and (Btwn$0 next$0 b$0 ?v ?v)
                                        (not (Btwn$0 next$0 b$0 l_5$0 l_5$0)))))
                          (and (not (= l_5$0 ?v))
                               (or (Btwn$0 next$0 ?z l_5$0 ?v)
                                   (and (Btwn$0 next$0 ?z l_5$0 l_5$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 b$0 ?u ?v)
                               (or (Btwn$0 next$0 b$0 ?v l_5$0)
                                   (and (Btwn$0 next$0 b$0 ?v ?v)
                                        (not (Btwn$0 next$0 b$0 l_5$0 l_5$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v l_5$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z l_5$0 l_5$0)))))
                 (and (not (= l_5$0 ?v))
                      (or (Btwn$0 next$0 ?z l_5$0 ?v)
                          (and (Btwn$0 next$0 ?z l_5$0 l_5$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u l_5$0)
                      (or (Btwn$0 next$0 b$0 ?v l_5$0)
                          (and (Btwn$0 next$0 b$0 ?v ?v)
                               (not (Btwn$0 next$0 b$0 l_5$0 l_5$0)))))
                 (and (not (= l_5$0 ?v))
                      (or (Btwn$0 next$0 ?z l_5$0 ?v)
                          (and (Btwn$0 next$0 ?z l_5$0 l_5$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 b$0 ?u ?v)
                      (or (Btwn$0 next$0 b$0 ?v l_5$0)
                          (and (Btwn$0 next$0 b$0 ?v ?v)
                               (not (Btwn$0 next$0 b$0 l_5$0 l_5$0)))))
                 (not (Btwn$0 (write$0 next$0 l_5$0 b$0) ?z ?u ?v))))) :named P89))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P90))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P92))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P93))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P94))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P95))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P96))

(check-sat)

(get-interpolants (and P14 P60 P18 P72 P42 P76 P79 P53 P5 P95 P57 P96 P84 P27 P17 P38 P65 P1 P2 P64 P93 P19 P66 P15 P58 P21 P20 P70 P8 P49 P29 P16 P94 P56 P32 P85 P34 P39 P62 P37 P25 P33 P92 P47 P59 P68 P28 P45 P44) (and P4 P23 P90 P40 P10 P86 P87 P51 P74 P46 P82 P9 P48 P75 P50 P78 P54 P81 P24 P11 P35 P61 P67 P69 P0 P7 P13 P36 P71 P6 P89 P83 P30 P80 P91 P88 P31 P12 P73 P52 P63 P77 P41 P3 P26 P55 P43 P22))

(exit)