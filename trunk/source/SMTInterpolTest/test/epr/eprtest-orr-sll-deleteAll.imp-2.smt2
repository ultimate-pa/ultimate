(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)

(set-logic UF)
(set-info :source |Second push block from orr-sanitized-eeaa/sll-deleteAll.imp.smt2|)
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


(assert (not (=> (forall ((x$2$1 V) (y$1$1 V)) (= (n* x$2$1 y$1$1) (_n* x$2$1 y$1$1))) (and (forall ((m$5$1 V) (w$15$1 V)) (=> (n* h m$5$1) (= (n* m$5$1 w$15$1) (_n* m$5$1 w$15$1)))) (forall ((m$6$1 V)) (=> (and (_n* h m$6$1) (not (_n* h m$6$1))) (or (and (n* m$6$1 null) (not (EQ m$6$1 null)) (forall ((w$16$1 V)) (=> (and (n* m$6$1 w$16$1) (not (EQ m$6$1 w$16$1))) (n* null w$16$1)))) (and (EQ null null) (forall ((w$17$1 V)) (not (and (n* m$6$1 w$17$1) (not (EQ m$6$1 w$17$1))))))))) (=> (not (EQ h null)) (_n* h h)) true))))

(check-sat)

(exit)
