(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)

(set-logic UF)
(set-info :source |First push block from orr/sll-last.imp.smt2|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort V 0)
(declare-fun i () V)
(declare-fun h () V)
(declare-fun n* (V V) Bool)
(declare-fun null () V)
(declare-fun j () V)

(declare-fun EQ (V V) Bool)
(assert (forall ((x V)) (EQ x x)))
(assert (forall ((x V) (y V)) (=> (EQ x y) (EQ y x))))
(assert (forall ((x V) (y V) (z V)) (=> (and (EQ x y) (EQ y z)) (EQ x z))))
(assert (forall ((x0 V) (y0 V) (x1 V) (y1 V)) (=> (and (EQ x0 y0) (EQ x1 y1)) (=> (n* x0 x1) (n* y0 y1)))))

(assert (forall ((u$1$1 V)) (n* u$1$1 u$1$1)))
(assert (forall ((u$2$1 V) (v$1$1 V) (w$1$1 V)) (=> (and (n* u$2$1 v$1$1) (n* v$1$1 w$1$1)) (n* u$2$1 w$1$1))))
(assert (forall ((u$3$1 V) (v$2$1 V) (w$2$1 V)) (=> (and (n* u$3$1 v$2$1) (n* u$3$1 w$2$1)) (or (n* v$2$1 w$2$1) (n* w$2$1 v$2$1)))))
(assert (forall ((u$4$1 V) (v$3$1 V)) (=> (n* u$4$1 v$3$1) (=> (n* v$3$1 u$4$1) (EQ u$4$1 v$3$1)))))
(assert (forall ((v$4$1 V)) (=> (or (n* null v$4$1) (n* v$4$1 null)) (EQ null v$4$1))))

(assert (not (=> (and (=> (not (EQ i null)) (n* h i)) (ite (EQ j null) (EQ i h) (and (n* h j) (or (and (n* j i) (not (EQ j i)) (forall ((w$3$1 V)) (=> (and (n* j w$3$1) (not (EQ j w$3$1))) (n* i w$3$1)))) (and (EQ i null) (forall ((w$4$1 V)) (not (and (n* j w$4$1) (not (EQ j w$4$1)))))))))) (ite (not (EQ i null)) (and (not (EQ i null)) (forall ((z$1$1 V)) (=> (or (and (n* i z$1$1) (not (EQ i z$1$1)) (forall ((w$5$1 V)) (=> (and (n* i w$5$1) (not (EQ i w$5$1))) (n* z$1$1 w$5$1)))) (and (EQ z$1$1 null) (forall ((w$6$1 V)) (not (and (n* i w$6$1) (not (EQ i w$6$1))))))) (and (=> (not (EQ z$1$1 null)) (n* h z$1$1)) (ite (EQ i null) (EQ z$1$1 h) (and (n* h i) (or (and (n* i z$1$1) (not (EQ i z$1$1)) (forall ((w$7$1 V)) (=> (and (n* i w$7$1) (not (EQ i w$7$1))) (n* z$1$1 w$7$1)))) (and (EQ z$1$1 null) (forall ((w$8$1 V)) (not (and (n* i w$8$1) (not (EQ i w$8$1))))))))))))) (ite (EQ h null) (EQ j null) (and (n* h j) (or (and (n* j null) (not (EQ j null)) (forall ((w$9$1 V)) (=> (and (n* j w$9$1) (not (EQ j w$9$1))) (n* null w$9$1)))) (and (EQ null null) (forall ((w$10$1 V)) (not (and (n* j w$10$1) (not (EQ j w$10$1)))))))))))))
(check-sat)

(exit)
