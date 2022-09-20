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
  tests/spl/union_find.spl:40:4-16:Possible heap access through null or dangling reference
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
(declare-fun Axiom_10$0 () Bool)
(declare-fun Axiom_11$0 () Bool)
(declare-fun Axiom_12$0 () Bool)
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun Axiom_15$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_7$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun X_1$0 () SetLoc)
(declare-fun X_28$0 () SetLoc)
(declare-fun X_29$0 () SetLoc)
(declare-fun Y$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_4$0 () FldLoc)
(declare-fun next_5$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
(declare-fun s_2$0 () Loc)
(declare-fun sk_?X_84$0 () SetLoc)
(declare-fun sk_?X_85$0 () SetLoc)
(declare-fun sk_?X_86$0 () SetLoc)
(declare-fun sk_?X_87$0 () SetLoc)
(declare-fun sk_?X_88$0 () SetLoc)
(declare-fun sk_?X_89$0 () SetLoc)
(declare-fun sk_?X_90$0 () SetLoc)
(declare-fun sk_?X_91$0 () SetLoc)
(declare-fun sk_?X_92$0 () SetLoc)
(declare-fun sk_?X_93$0 () SetLoc)
(declare-fun sk_?X_94$0 () SetLoc)
(declare-fun sk_?X_95$0 () SetLoc)
(declare-fun sk_?X_96$0 () SetLoc)
(declare-fun sk_?X_97$0 () SetLoc)
(declare-fun sk_?X_98$0 () SetLoc)
(declare-fun sk_?X_99$0 () SetLoc)
(declare-fun sk_?X_100$0 () SetLoc)
(declare-fun sk_?X_101$0 () SetLoc)
(declare-fun sk_?X_102$0 () SetLoc)
(declare-fun sk_?X_103$0 () SetLoc)
(declare-fun sk_?X_104$0 () SetLoc)
(declare-fun sk_?X_105$0 () SetLoc)
(declare-fun sk_?X_106$0 () SetLoc)
(declare-fun sk_?X_107$0 () SetLoc)
(declare-fun sk_?X_108$0 () SetLoc)
(declare-fun sk_?X_109$0 () SetLoc)
(declare-fun sk_?X_110$0 () SetLoc)
(declare-fun sk_?X_111$0 () SetLoc)
(declare-fun sk_?X_112$0 () SetLoc)
(declare-fun t_2$0 () Loc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next$0 s_2$0 (read$0 next$0 s_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next_4$0 s_2$0 (read$0 next_4$0 s_2$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next_5$0 s_2$0 (read$0 next_5$0 s_2$0) ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next_5$0 t_2$0 (read$0 next_5$0 t_2$0) ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 t_2$0) t_2$0))
            (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y))) :named P9))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 s_2$0) s_2$0))
            (not (Btwn$0 next$0 s_2$0 ?y ?y)) (= s_2$0 ?y))) :named P10))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P11))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 t_2$0) t_2$0))
            (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y))) :named P12))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 s_2$0) s_2$0))
            (not (Btwn$0 next_4$0 s_2$0 ?y ?y)) (= s_2$0 ?y))) :named P13))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 null$0) null$0))
            (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y))) :named P14))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 s_2$0) s_2$0))
            (not (Btwn$0 next_5$0 s_2$0 ?y ?y)) (= s_2$0 ?y))) :named P15))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 null$0) null$0))
            (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y))) :named P16))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 t_2$0) t_2$0))
            (not (Btwn$0 next_5$0 t_2$0 ?y ?y)) (= t_2$0 ?y))) :named P17))

(assert (! (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) (read$0 next$0 t_2$0)) :named P18))

(assert (! (Btwn$0 next$0 s_2$0 (read$0 next$0 s_2$0) (read$0 next$0 s_2$0)) :named P19))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P20))

(assert (! (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) (read$0 next_4$0 t_2$0)) :named P21))

(assert (! (Btwn$0 next_4$0 s_2$0 (read$0 next_4$0 s_2$0) (read$0 next_4$0 s_2$0)) :named P22))

(assert (! (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) (read$0 next_4$0 null$0)) :named P23))

(assert (! (Btwn$0 next_5$0 s_2$0 (read$0 next_5$0 s_2$0) (read$0 next_5$0 s_2$0)) :named P24))

(assert (! (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) (read$0 next_5$0 null$0)) :named P25))

(assert (! (Btwn$0 next_5$0 t_2$0 (read$0 next_5$0 t_2$0) (read$0 next_5$0 t_2$0)) :named P26))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 next$0 t_2$0) (read$0 next_4$0 t_2$0))
        (not (in$0 t_2$0 (setminus$0 Alloc$0 FP_4$0))))) :named P27))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 next$0 s_2$0) (read$0 next_4$0 s_2$0))
        (not (in$0 s_2$0 (setminus$0 Alloc$0 FP_4$0))))) :named P28))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 next$0 null$0) (read$0 next_4$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_4$0))))) :named P29))

(assert (! (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_4$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_4$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_4$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_4$0 null$0)
                                     (ep$0 next$0 FP_4$0 null$0))))))))) :named P30))

(assert (! (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 t_2$0 ?z ?y)
                     (Btwn$0 next_4$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_4$0 t_2$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 t_2$0 ?y (ep$0 next$0 FP_4$0 t_2$0))
                         (and (Btwn$0 next$0 t_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 t_2$0
                                     (ep$0 next$0 FP_4$0 t_2$0)
                                     (ep$0 next$0 FP_4$0 t_2$0))))))))) :named P31))

(assert (! (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 x_1$0 ?z ?y)
                     (Btwn$0 next_4$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_4$0 x_1$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 x_1$0 ?y (ep$0 next$0 FP_4$0 x_1$0))
                         (and (Btwn$0 next$0 x_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 x_1$0
                                     (ep$0 next$0 FP_4$0 x_1$0)
                                     (ep$0 next$0 FP_4$0 x_1$0))))))))) :named P32))

(assert (! (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 y$0 ?z ?y) (Btwn$0 next_4$0 y$0 ?z ?y))
                (and (not (Btwn$0 next$0 y$0 ?z ?y))
                     (not (Btwn$0 next_4$0 y$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 y$0 ?y (ep$0 next$0 FP_4$0 y$0))
                         (and (Btwn$0 next$0 y$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 y$0
                                     (ep$0 next$0 FP_4$0 y$0)
                                     (ep$0 next$0 FP_4$0 y$0))))))))) :named P33))

(assert (! (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_4$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_4$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_4$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_4$0 null$0)))))) :named P34))

(assert (! (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 t_2$0 FP_4$0)
                (and (Btwn$0 next$0 t_2$0 ?z ?y)
                     (Btwn$0 next_4$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_4$0 t_2$0 ?z ?y)))
                (not (= t_2$0 (ep$0 next$0 FP_4$0 t_2$0)))))) :named P35))

(assert (! (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x_1$0 FP_4$0)
                (and (Btwn$0 next$0 x_1$0 ?z ?y)
                     (Btwn$0 next_4$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_4$0 x_1$0 ?z ?y)))
                (not (= x_1$0 (ep$0 next$0 FP_4$0 x_1$0)))))) :named P36))

(assert (! (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 y$0 FP_4$0)
                (and (Btwn$0 next$0 y$0 ?z ?y) (Btwn$0 next_4$0 y$0 ?z ?y))
                (and (not (Btwn$0 next$0 y$0 ?z ?y))
                     (not (Btwn$0 next_4$0 y$0 ?z ?y)))
                (not (= y$0 (ep$0 next$0 FP_4$0 y$0)))))) :named P37))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next_4$0 null$0 (ep$0 next_4$0 FP_6$0 null$0) ?y)
            (not (Btwn$0 next_4$0 null$0 ?y ?y)) (not (in$0 ?y FP_6$0)))) :named P38))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next_4$0 t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0) ?y)
            (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (not (in$0 ?y FP_6$0)))) :named P39))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next_4$0 x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0) ?y)
            (not (Btwn$0 next_4$0 x_1$0 ?y ?y)) (not (in$0 ?y FP_6$0)))) :named P40))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next_4$0 y$0 (ep$0 next_4$0 FP_6$0 y$0) ?y)
            (not (Btwn$0 next_4$0 y$0 ?y ?y)) (not (in$0 ?y FP_6$0)))) :named P41))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_109$0 null$0) sk_?X_109$0)
    (= null$0 (ep$0 next$0 sk_?X_109$0 null$0))) :named P42))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_109$0 t_2$0) sk_?X_109$0)
    (= t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0))) :named P43))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_109$0 x_1$0) sk_?X_109$0)
    (= x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0))) :named P44))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_109$0 y$0) sk_?X_109$0)
    (= y$0 (ep$0 next$0 sk_?X_109$0 y$0))) :named P45))

(assert (! (Btwn$0 next_4$0 null$0 (ep$0 next_4$0 FP_6$0 null$0)
  (ep$0 next_4$0 FP_6$0 null$0)) :named P46))

(assert (! (Btwn$0 next_4$0 t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0)
  (ep$0 next_4$0 FP_6$0 t_2$0)) :named P47))

(assert (! (Btwn$0 next_4$0 x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0)
  (ep$0 next_4$0 FP_6$0 x_1$0)) :named P48))

(assert (! (Btwn$0 next_4$0 y$0 (ep$0 next_4$0 FP_6$0 y$0) (ep$0 next_4$0 FP_6$0 y$0)) :named P49))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 s_2$0) (read$0 next_5$0 s_2$0))
        (not (in$0 s_2$0 (setminus$0 Alloc$0 FP_6$0))))) :named P50))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 null$0) (read$0 next_5$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_6$0))))) :named P51))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 t_2$0) (read$0 next_5$0 t_2$0))
        (not (in$0 t_2$0 (setminus$0 Alloc$0 FP_6$0))))) :named P52))

(assert (! (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 null$0 ?y
                           (ep$0 next_4$0 FP_6$0 null$0))
                         (and (Btwn$0 next_4$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 null$0
                                     (ep$0 next_4$0 FP_6$0 null$0)
                                     (ep$0 next_4$0 FP_6$0 null$0))))))))) :named P53))

(assert (! (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 t_2$0 ?z ?y)
                     (Btwn$0 next_5$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_5$0 t_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 t_2$0 ?y
                           (ep$0 next_4$0 FP_6$0 t_2$0))
                         (and (Btwn$0 next_4$0 t_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 t_2$0
                                     (ep$0 next_4$0 FP_6$0 t_2$0)
                                     (ep$0 next_4$0 FP_6$0 t_2$0))))))))) :named P54))

(assert (! (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 x_1$0 ?z ?y)
                     (Btwn$0 next_5$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 x_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 x_1$0 ?y
                           (ep$0 next_4$0 FP_6$0 x_1$0))
                         (and (Btwn$0 next_4$0 x_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 x_1$0
                                     (ep$0 next_4$0 FP_6$0 x_1$0)
                                     (ep$0 next_4$0 FP_6$0 x_1$0))))))))) :named P55))

(assert (! (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next_4$0 y$0 ?z ?y) (Btwn$0 next_5$0 y$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 y$0 ?z ?y))
                     (not (Btwn$0 next_5$0 y$0 ?z ?y)))
                (not
                     (or (Btwn$0 next_4$0 y$0 ?y (ep$0 next_4$0 FP_6$0 y$0))
                         (and (Btwn$0 next_4$0 y$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 y$0
                                     (ep$0 next_4$0 FP_6$0 y$0)
                                     (ep$0 next_4$0 FP_6$0 y$0))))))))) :named P56))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_6$0)
                (and (Btwn$0 next_4$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next_4$0 FP_6$0 null$0)))))) :named P57))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 t_2$0 FP_6$0)
                (and (Btwn$0 next_4$0 t_2$0 ?z ?y)
                     (Btwn$0 next_5$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_5$0 t_2$0 ?z ?y)))
                (not (= t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0)))))) :named P58))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x_1$0 FP_6$0)
                (and (Btwn$0 next_4$0 x_1$0 ?z ?y)
                     (Btwn$0 next_5$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 x_1$0 ?z ?y)))
                (not (= x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0)))))) :named P59))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 y$0 FP_6$0)
                (and (Btwn$0 next_4$0 y$0 ?z ?y) (Btwn$0 next_5$0 y$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 y$0 ?z ?y))
                     (not (Btwn$0 next_5$0 y$0 ?z ?y)))
                (not (= y$0 (ep$0 next_4$0 FP_6$0 y$0)))))) :named P60))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_109$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))) :named P61))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0) ?y)
            (not (Btwn$0 next$0 t_2$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))) :named P62))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0) ?y)
            (not (Btwn$0 next$0 x_1$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))) :named P63))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_109$0 y$0) ?y)
            (not (Btwn$0 next$0 y$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))) :named P64))

(assert (! (or (in$0 (ep$0 next_4$0 FP_6$0 null$0) FP_6$0)
    (= null$0 (ep$0 next_4$0 FP_6$0 null$0))) :named P65))

(assert (! (or (in$0 (ep$0 next_4$0 FP_6$0 t_2$0) FP_6$0)
    (= t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0))) :named P66))

(assert (! (or (in$0 (ep$0 next_4$0 FP_6$0 x_1$0) FP_6$0)
    (= x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0))) :named P67))

(assert (! (or (in$0 (ep$0 next_4$0 FP_6$0 y$0) FP_6$0)
    (= y$0 (ep$0 next_4$0 FP_6$0 y$0))) :named P68))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_109$0 null$0)
  (ep$0 next$0 sk_?X_109$0 null$0)) :named P69))

(assert (! (Btwn$0 next$0 t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0)
  (ep$0 next$0 sk_?X_109$0 t_2$0)) :named P70))

(assert (! (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0)
  (ep$0 next$0 sk_?X_109$0 x_1$0)) :named P71))

(assert (! (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_109$0 y$0)
  (ep$0 next$0 sk_?X_109$0 y$0)) :named P72))

(assert (! (or (= (read$0 next_5$0 s_2$0) root_y$0) (not (in$0 s_2$0 X_29$0))) :named P73))

(assert (! (or (= (read$0 next_5$0 null$0) root_y$0) (not (in$0 null$0 X_29$0))) :named P74))

(assert (! (or (= (read$0 next_5$0 t_2$0) root_y$0) (not (in$0 t_2$0 X_29$0))) :named P75))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P76))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_7$0 Alloc$0))
                 (or (in$0 x FP_7$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_7$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_7$0 Alloc$0)))))) :named P77))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_5$0 Alloc$0))
                 (or (in$0 x FP_5$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_5$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_5$0 Alloc$0)))))) :named P78))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_6$0 FP_5$0))
                 (or (in$0 x FP_6$0) (in$0 x FP_5$0)))
            (and (not (in$0 x FP_6$0)) (not (in$0 x FP_5$0))
                 (not (in$0 x (union$0 FP_6$0 FP_5$0)))))) :named P79))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_104$0))
                 (or (in$0 x (setminus$0 FP$0 FP_4$0)) (in$0 x sk_?X_104$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_4$0)))
                 (not (in$0 x sk_?X_104$0))
                 (not
                      (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_104$0)))))) :named P80))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_108$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_108$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_108$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_108$0 sk_?X_106$0)))))) :named P81))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP_5$0 FP_6$0) sk_?X_97$0))
                 (or (in$0 x (setminus$0 FP_5$0 FP_6$0)) (in$0 x sk_?X_97$0)))
            (and (not (in$0 x (setminus$0 FP_5$0 FP_6$0)))
                 (not (in$0 x sk_?X_97$0))
                 (not
                      (in$0 x
                        (union$0 (setminus$0 FP_5$0 FP_6$0) sk_?X_97$0)))))) :named P82))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_84$0 FP_Caller$0))
                 (or (in$0 x sk_?X_84$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_84$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_84$0 FP_Caller$0)))))) :named P83))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_109$0 sk_?X_84$0))
                 (or (in$0 x sk_?X_109$0) (in$0 x sk_?X_84$0)))
            (and (not (in$0 x sk_?X_109$0)) (not (in$0 x sk_?X_84$0))
                 (not (in$0 x (union$0 sk_?X_109$0 sk_?X_84$0)))))) :named P84))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_90$0 sk_?X_85$0))
                 (or (in$0 x sk_?X_90$0) (in$0 x sk_?X_85$0)))
            (and (not (in$0 x sk_?X_90$0)) (not (in$0 x sk_?X_85$0))
                 (not (in$0 x (union$0 sk_?X_90$0 sk_?X_85$0)))))) :named P85))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_89$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_89$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_89$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_89$0 sk_?X_106$0)))))) :named P86))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_92$0 sk_?X_91$0))
                 (or (in$0 x sk_?X_92$0) (in$0 x sk_?X_91$0)))
            (and (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_91$0))
                 (not (in$0 x (union$0 sk_?X_92$0 sk_?X_91$0)))))) :named P87))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_93$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_93$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_93$0 sk_?X_106$0)))))) :named P88))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P89))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_99$0 sk_?X_89$0))
                 (or (in$0 x sk_?X_99$0) (in$0 x sk_?X_89$0)))
            (and (not (in$0 x sk_?X_99$0)) (not (in$0 x sk_?X_89$0))
                 (not (in$0 x (union$0 sk_?X_99$0 sk_?X_89$0)))))) :named P90))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_4$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_4$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_4$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_4$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P91))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_92$0 sk_?X_89$0))
                 (or (in$0 x sk_?X_92$0) (in$0 x sk_?X_89$0)))
            (and (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_89$0))
                 (not (in$0 x (union$0 sk_?X_92$0 sk_?X_89$0)))))) :named P92))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_108$0) (in$0 x sk_?X_106$0)
                 (in$0 x (intersection$0 sk_?X_108$0 sk_?X_106$0)))
            (and (or (not (in$0 x sk_?X_108$0)) (not (in$0 x sk_?X_106$0)))
                 (not (in$0 x (intersection$0 sk_?X_108$0 sk_?X_106$0)))))) :named P93))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_99$0) (in$0 x sk_?X_89$0)
                 (in$0 x (intersection$0 sk_?X_99$0 sk_?X_89$0)))
            (and (or (not (in$0 x sk_?X_99$0)) (not (in$0 x sk_?X_89$0)))
                 (not (in$0 x (intersection$0 sk_?X_99$0 sk_?X_89$0)))))) :named P94))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_93$0) (in$0 x sk_?X_106$0)
                 (in$0 x (intersection$0 sk_?X_93$0 sk_?X_106$0)))
            (and (or (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_106$0)))
                 (not (in$0 x (intersection$0 sk_?X_93$0 sk_?X_106$0)))))) :named P95))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_92$0) (in$0 x sk_?X_89$0)
                 (in$0 x (intersection$0 sk_?X_92$0 sk_?X_89$0)))
            (and (or (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_89$0)))
                 (not (in$0 x (intersection$0 sk_?X_92$0 sk_?X_89$0)))))) :named P96))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_90$0) (in$0 x sk_?X_85$0)
                 (in$0 x (intersection$0 sk_?X_90$0 sk_?X_85$0)))
            (and (or (not (in$0 x sk_?X_90$0)) (not (in$0 x sk_?X_85$0)))
                 (not (in$0 x (intersection$0 sk_?X_90$0 sk_?X_85$0)))))) :named P97))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_109$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_109$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_109$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_109$0)))))) :named P98))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_6$0)
                 (in$0 x (intersection$0 Alloc$0 FP_6$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_6$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_6$0)))))) :named P99))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P100))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_109$0))
                 (not (in$0 x sk_?X_109$0)))
            (and (or (in$0 x sk_?X_109$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_109$0)))))) :named P101))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_6$0))
                 (not (in$0 x FP_6$0)))
            (and (or (in$0 x FP_6$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_6$0)))))) :named P102))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_84$0)
                 (in$0 x (setminus$0 sk_?X_84$0 sk_?X_109$0))
                 (not (in$0 x sk_?X_109$0)))
            (and (or (in$0 x sk_?X_109$0) (not (in$0 x sk_?X_84$0)))
                 (not (in$0 x (setminus$0 sk_?X_84$0 sk_?X_109$0)))))) :named P103))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_5$0) (in$0 x (setminus$0 FP_5$0 FP_6$0))
                 (not (in$0 x FP_6$0)))
            (and (or (in$0 x FP_6$0) (not (in$0 x FP_5$0)))
                 (not (in$0 x (setminus$0 FP_5$0 FP_6$0)))))) :named P104))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_84$0))
                 (not (in$0 x sk_?X_84$0)))
            (and (or (in$0 x sk_?X_84$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_84$0)))))) :named P105))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P106))

(assert (! (= (read$0 next$0 null$0) null$0) :named P107))

(assert (! (= (read$0 next_4$0 null$0) null$0) :named P108))

(assert (! (= (read$0 next_5$0 null$0) null$0) :named P109))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P110))

(assert (! (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_92$0 next$0 x_1$0 root_x_1$0 X_1$0))) :named P111))

(assert (! (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_91$0 next$0 y$0 root_y$0 Y$0))) :named P112))

(assert (! (= FP_5$0
  (union$0 (setminus$0 FP$0 FP_4$0)
    (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0)))) :named P113))

(assert (! (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)) :named P114))

(assert (! (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0) :named P115))

(assert (! (= Alloc$0 (union$0 FP_7$0 Alloc$0)) :named P116))

(assert (! (= (read$0 next$0 root_x_1$0) null$0) :named P117))

(assert (! (= emptyset$0 emptyset$0) :named P118))

(assert (! (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)) :named P119))

(assert (! (= sk_?X_84$0 (union$0 sk_?X_90$0 sk_?X_85$0)) :named P120))

(assert (! (= sk_?X_85$0 (union$0 sk_?X_88$0 sk_?X_86$0)) :named P121))

(assert (! (= sk_?X_87$0 (setenum$0 root_y$0)) :named P122))

(assert (! (= sk_?X_89$0 (setenum$0 root_x_1$0)) :named P123))

(assert (! (= sk_?X_91$0 (lseg_set_domain$0 next$0 y$0 root_y$0)) :named P124))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P125))

(assert (! (lseg_set_struct$0 sk_?X_92$0 next$0 x_1$0 root_x_1$0 X_1$0) :named P126))

(assert (! (= emptyset$0 emptyset$0) :named P127))

(assert (! (= X_28$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)) :named P128))

(assert (! (= sk_?X_109$0 FP_4$0) :named P129))

(assert (! (= sk_?X_111$0 (setenum$0 root_x_1$0)) :named P130))

(assert (! (= FP$0 (union$0 FP_4$0 FP$0)) :named P131))

(assert (! (= (read$0 next_4$0 root_x_1$0) null$0) :named P132))

(assert (! (= emptyset$0 (intersection$0 sk_?X_99$0 sk_?X_101$0)) :named P133))

(assert (! (= sk_?X_100$0 (setenum$0 root_x_1$0)) :named P134))

(assert (! (= sk_?X_102$0 (union$0 sk_?X_99$0 sk_?X_101$0)) :named P135))

(assert (! (= sk_?X_104$0
  (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0))) :named P136))

(assert (! (= t_2$0 root_x_1$0) :named P137))

(assert (! (= (read$0 next_4$0 root_y$0) null$0) :named P138))

(assert (! (= emptyset$0 (intersection$0 sk_?X_108$0 sk_?X_106$0)) :named P139))

(assert (! (= sk_?X_105$0 (union$0 sk_?X_108$0 sk_?X_106$0)) :named P140))

(assert (! (= sk_?X_106$0 sk_?X_107$0) :named P141))

(assert (! (= sk_?X_108$0 (lseg_set_domain$0 next_4$0 y$0 root_y$0)) :named P142))

(assert (! (lseg_set_struct$0 sk_?X_108$0 next_4$0 y$0 root_y$0 X_29$0) :named P143))

(assert (! (= emptyset$0 emptyset$0) :named P144))

(assert (! (= s_2$0 root_y$0) :named P145))

(assert (! (= sk_?X_94$0 (setenum$0 root_y$0)) :named P146))

(assert (! (= sk_?X_96$0 (union$0 sk_?X_93$0 sk_?X_95$0)) :named P147))

(assert (! (= sk_?X_98$0
  (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0))) :named P148))

(assert (! (not (in$0 null$0 Alloc$0)) :named P149))

(assert (! (not (in$0 null$0 Alloc$0)) :named P150))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))))) :named P151))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0)))))) :named P152))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_X$0 next_4$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next_4$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_X$0 next_4$0 y$0 root_y$0)))))) :named P153))

(assert (! (or (and Axiom_15$0 Axiom_14$0 Axiom_13$0)
    (not (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))) :named P154))

(assert (! (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_112$0 next$0 x_1$0 root_x_1$0 X_28$0))) :named P155))

(assert (! (or (Btwn$0 next_4$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_108$0 next_4$0 y$0 root_y$0 X_29$0))) :named P156))

(assert (! (= FP_7$0
  (union$0 (setminus$0 FP_5$0 FP_6$0)
    (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0)))) :named P157))

(assert (! (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0) :named P158))

(assert (! (= Alloc$0 (union$0 FP_5$0 Alloc$0)) :named P159))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P160))

(assert (! (= (read$0 next$0 root_y$0) null$0) :named P161))

(assert (! (= emptyset$0 (intersection$0 sk_?X_90$0 sk_?X_85$0)) :named P162))

(assert (! (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)) :named P163))

(assert (! (= sk_?X_84$0 FP$0) :named P164))

(assert (! (= sk_?X_86$0 sk_?X_87$0) :named P165))

(assert (! (= sk_?X_88$0 sk_?X_89$0) :named P166))

(assert (! (= sk_?X_90$0 (union$0 sk_?X_92$0 sk_?X_91$0)) :named P167))

(assert (! (= sk_?X_92$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)) :named P168))

(assert (! (lseg_set_struct$0 sk_?X_91$0 next$0 y$0 root_y$0 Y$0) :named P169))

(assert (! (= (read$0 next$0 root_x_1$0) null$0) :named P170))

(assert (! (= emptyset$0 (intersection$0 sk_?X_112$0 sk_?X_110$0)) :named P171))

(assert (! (= sk_?X_109$0 (union$0 sk_?X_112$0 sk_?X_110$0)) :named P172))

(assert (! (= sk_?X_110$0 sk_?X_111$0) :named P173))

(assert (! (= sk_?X_112$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)) :named P174))

(assert (! (lseg_set_struct$0 sk_?X_112$0 next$0 x_1$0 root_x_1$0 X_28$0) :named P175))

(assert (! (= emptyset$0 emptyset$0) :named P176))

(assert (! (= sk_?X_99$0 X_28$0) :named P177))

(assert (! (= sk_?X_101$0 sk_?X_100$0) :named P178))

(assert (! (= sk_?X_103$0 sk_?X_102$0) :named P179))

(assert (! (= sk_?X_104$0 sk_?X_103$0) :named P180))

(assert (! (forall ((z Loc))
        (or
            (and (Btwn$0 next_4$0 z root_x_1$0 root_x_1$0)
                 (forall ((?x Loc))
                         (or (= ?x z) (= ?x root_x_1$0)
                             (not (Btwn$0 next_4$0 z ?x root_x_1$0)))))
            (not (in$0 z X_28$0)))) :named P181))

(assert (! (= emptyset$0 emptyset$0) :named P182))

(assert (! (= X_29$0 (lseg_set_X$0 next_4$0 y$0 root_y$0)) :named P183))

(assert (! (= sk_?X_105$0 FP_6$0) :named P184))

(assert (! (= sk_?X_107$0 (setenum$0 root_y$0)) :named P185))

(assert (! (= FP_5$0 (union$0 FP_6$0 FP_5$0)) :named P186))

(assert (! (= (read$0 next_5$0 root_y$0) null$0) :named P187))

(assert (! (= emptyset$0 (intersection$0 sk_?X_93$0 sk_?X_95$0)) :named P188))

(assert (! (= sk_?X_93$0 X_29$0) :named P189))

(assert (! (= sk_?X_95$0 sk_?X_94$0) :named P190))

(assert (! (= sk_?X_97$0 sk_?X_96$0) :named P191))

(assert (! (= sk_?X_98$0 sk_?X_97$0) :named P192))

(assert (! (not (= t_2$0 s_2$0)) :named P193))

(assert (! (not (in$0 null$0 Alloc$0)) :named P194))

(assert (! (not (in$0 t_2$0 FP_7$0)) :named P195))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))))) :named P196))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0)))))) :named P197))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_domain$0 next_4$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next_4$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next_4$0 y$0 root_y$0)))))) :named P198))

(assert (! (or (and Axiom_12$0 Axiom_11$0 Axiom_10$0)
    (not (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0))) :named P199))

(assert (! (forall ((?x Loc)) (Btwn$0 next_5$0 ?x ?x ?x)) :named P200))

(assert (! (forall ((?x Loc)) (Btwn$0 next_4$0 ?x ?x ?x)) :named P201))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P202))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_5$0 ?x ?y ?x)) (= ?x ?y))) :named P203))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_4$0 ?x ?y ?x)) (= ?x ?y))) :named P204))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P205))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?x ?z ?z))
            (Btwn$0 next_5$0 ?x ?y ?z) (Btwn$0 next_5$0 ?x ?z ?y))) :named P206))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?x ?z ?z))
            (Btwn$0 next_4$0 ?x ?y ?z) (Btwn$0 next_4$0 ?x ?z ?y))) :named P207))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P208))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?y) (Btwn$0 next_5$0 ?y ?z ?z)))) :named P209))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?y) (Btwn$0 next_4$0 ?y ?z ?z)))) :named P210))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P211))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?y ?z ?z))
            (Btwn$0 next_5$0 ?x ?z ?z))) :named P212))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?y ?z ?z))
            (Btwn$0 next_4$0 ?x ?z ?z))) :named P213))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P214))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?y ?u ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?u) (Btwn$0 next_5$0 ?x ?u ?z)))) :named P215))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?y ?u ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?u) (Btwn$0 next_4$0 ?x ?u ?z)))) :named P216))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P217))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?x ?u ?y))
            (and (Btwn$0 next_5$0 ?x ?u ?z) (Btwn$0 next_5$0 ?u ?y ?z)))) :named P218))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?x ?u ?y))
            (and (Btwn$0 next_4$0 ?x ?u ?z) (Btwn$0 next_4$0 ?u ?y ?z)))) :named P219))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P220))

(check-sat)

(get-interpolants (and P16 P77 P144 P82 P209 P79 P78 P24 P65 P13 P102 P47 P135 P188 P34 P136 P28 P73 P194 P183 P217 P202 P23 P172 P128 P112 P168 P56 P74 P109 P3 P83 P192 P29 P58 P150 P110 P49 P207 P132 P171 P41 P193 P216 P122 P59 P17 P39 P66 P68 P160 P93 P48 P143 P185 P159 P219 P72 P198 P89 P27 P50 P123 P200 P169 P218 P120 P38 P177 P191 P187 P119 P107 P45 P210 P21 P42 P62 P55 P2 P195 P181 P152 P121 P137 P14 P118 P126 P154 P18 P8 P70 P190 P64 P53 P25 P204 P116 P31 P173 P11 P84 P157 P33 P75 P129 P167 P5 P111 P180 P76) (and P203 P106 P98 P104 P105 P15 P184 P179 P176 P51 P139 P100 P124 P117 P71 P80 P12 P178 P142 P145 P85 P113 P133 P99 P69 P211 P151 P182 P6 P127 P30 P4 P87 P0 P220 P156 P146 P161 P170 P95 P214 P147 P22 P81 P115 P46 P86 P32 P36 P175 P165 P94 P114 P37 P197 P134 P101 P205 P153 P54 P131 P141 P90 P148 P60 P149 P125 P189 P40 P215 P26 P57 P91 P63 P163 P213 P96 P88 P166 P61 P155 P20 P67 P208 P199 P140 P10 P19 P103 P130 P186 P35 P174 P7 P158 P164 P92 P162 P44 P196 P212 P201 P138 P108 P1 P206 P52 P43 P9 P97))

(exit)