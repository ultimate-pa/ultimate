(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)

(set-logic UF)
(set-info :source |First push block from orr-sanitized-eeaa/sll-deleteAll.imp.smt2|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort V 0)
(declare-fun n* (V V) Bool)
(declare-fun i () V)
(declare-fun h () V)
(declare-fun j () V)
(declare-fun _n* (V V) Bool)
(declare-fun null () V)

(declare-fun EQ (V V) Bool)
(assert (forall ((x V)) (EQ x x)))
(assert (forall ((x V) (y V)) (=> (EQ x y) (EQ y x))))
(assert (forall ((x V) (y V) (z V)) (=> (and (EQ x y) (EQ y z)) (EQ x z))))
(assert (forall ((x0 V) (y0 V) (x1 V) (y1 V)) (=> (and (EQ x0 y0) (EQ x1 y1)) (=> (_n* x0 x1) (_n* y0 y1)))))
(assert (forall ((x0 V) (y0 V) (x1 V) (y1 V)) (=> (and (EQ x0 y0) (EQ x1 y1)) (=> (n* x0 x1) (n* y0 y1)))))

(assert (forall ((u$1$1 V)) (n* u$1$1 u$1$1)))
(assert (forall ((u$2$1 V) (v$1$1 V) (w$1$1 V)) (=> (and (n* u$2$1 v$1$1) (n* v$1$1 w$1$1)) (n* u$2$1 w$1$1))))
(assert (forall ((u$3$1 V) (v$2$1 V) (w$2$1 V)) (=> (and (n* u$3$1 v$2$1) (n* u$3$1 w$2$1)) (or (n* v$2$1 w$2$1) (n* w$2$1 v$2$1)))))
(assert (forall ((u$4$1 V) (v$3$1 V)) (=> (n* u$4$1 v$3$1) (=> (n* v$3$1 u$4$1) (EQ u$4$1 v$3$1)))))
(assert (forall ((v$4$1 V)) (=> (or (n* null v$4$1) (n* v$4$1 null)) (EQ null v$4$1))))
(assert (forall ((u$5$1 V)) (_n* u$5$1 u$5$1)))
(assert (forall ((u$6$1 V) (v$5$1 V) (w$3$1 V)) (=> (and (_n* u$6$1 v$5$1) (_n* v$5$1 w$3$1)) (_n* u$6$1 w$3$1))))
(assert (forall ((u$7$1 V) (v$6$1 V) (w$4$1 V)) (=> (and (_n* u$7$1 v$6$1) (_n* u$7$1 w$4$1)) (or (_n* v$6$1 w$4$1) (_n* w$4$1 v$6$1)))))
(assert (forall ((u$8$1 V) (v$7$1 V)) (=> (_n* u$8$1 v$7$1) (=> (_n* v$7$1 u$8$1) (EQ u$8$1 v$7$1)))))
(assert (forall ((v$8$1 V)) (=> (or (_n* null v$8$1) (_n* v$8$1 null)) (EQ null v$8$1))))


(assert (not (=> (and (forall ((m$1$1 V) (w$5$1 V)) (=> (n* i m$1$1) (= (n* m$1$1 w$5$1) (_n* m$1$1 w$5$1)))) (forall ((m$2$1 V)) (=> (and (_n* h m$2$1) (not (_n* i m$2$1))) (or (and (n* m$2$1 null) (not (EQ m$2$1 null)) (forall ((w$6$1 V)) (=> (and (n* m$2$1 w$6$1) (not (EQ m$2$1 w$6$1))) (n* null w$6$1)))) (and (EQ null null) (forall ((w$7$1 V)) (not (and (n* m$2$1 w$7$1) (not (EQ m$2$1 w$7$1))))))))) (=> (not (EQ i null)) (_n* h i))) (ite (not (EQ i null)) (and (not (EQ i null)) (forall ((z$1$1 V)) (=> (or (and (n* i z$1$1) (not (EQ i z$1$1)) (forall ((w$8$1 V)) (=> (and (n* i w$8$1) (not (EQ i w$8$1))) (n* z$1$1 w$8$1)))) (and (EQ z$1$1 null) (forall ((w$9$1 V)) (not (and (n* i w$9$1) (not (EQ i w$9$1))))))) (and (forall ((m$3$1 V) (w$10$1 V)) (=> (and (n* z$1$1 m$3$1) (or (not (n* z$1$1 i)) (n* m$3$1 i))) (= (and (n* m$3$1 w$10$1) (or (not (n* m$3$1 i)) (n* w$10$1 i))) (_n* m$3$1 w$10$1)))) (forall ((m$4$1 V)) (=> (and (_n* h m$4$1) (not (_n* z$1$1 m$4$1))) (or (and (n* m$4$1 null) (or (not (n* m$4$1 i)) (n* null i)) (not (EQ m$4$1 null)) (forall ((w$11$1 V)) (=> (and (n* m$4$1 w$11$1) (or (not (n* m$4$1 i)) (n* w$11$1 i)) (not (EQ m$4$1 w$11$1))) (and (n* null w$11$1) (or (not (n* null i)) (n* w$11$1 i)))))) (and (EQ null null) (forall ((w$12$1 V)) (not (and (n* m$4$1 w$12$1) (or (not (n* m$4$1 i)) (n* w$12$1 i)) (not (EQ m$4$1 w$12$1))))))))) (=> (not (EQ z$1$1 null)) (_n* h z$1$1)))))) (forall ((x$1$1 V)) (=> (_n* h x$1$1) (or (and (n* x$1$1 null) (not (EQ x$1$1 null)) (forall ((w$13$1 V)) (=> (and (n* x$1$1 w$13$1) (not (EQ x$1$1 w$13$1))) (n* null w$13$1)))) (and (EQ null null) (forall ((w$14$1 V)) (not (and (n* x$1$1 w$14$1) (not (EQ x$1$1 w$14$1)))))))))))))

(check-sat)

(exit)
